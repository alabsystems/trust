// trust-lift: Semantic lifting — convert machine Effects to TrustIr Statements
//
// This module bridges trust-machine-sem (instruction semantics as Effects) with
// trust-types (TrustIr Statements). Each Effect becomes one or more TrustIr Statements
// that faithfully represent the instruction's behavior in the verification IR.
//
// Trust: #573 — architecture-aware semantic lifting (AArch64 + x86_64).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::{
    ControlFlow, Instruction, Opcode,
    operand::{
        BarrierDomain, BarrierType, Condition, ExtendType, MemoryOperand as DisasmMemoryOperand,
        Operand as DisasmOperand, RegKind, Register,
    },
};
use trust_machine_sem::{
    Aarch64Semantics, Effect, MachineState, SemError, Semantics, X86_64Semantics,
};
use trust_types::{
    AssertMessage, BasicBlock as TrustIrBlock, BinaryOrigin, BlockId, ConstValue, Endianness, Formula,
    LocalDecl, MemoryAccessFact, MemoryAccessKind, MemoryRegionKind, Operand, Place, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnsupportedLedger, UnsupportedRecord, stable_sha256_hex,
};

use crate::cfg::{Cfg, CfgEdge, CfgEdgeKind, CfgEdgeTarget, LiftedBlock};
use crate::error::{LiftError, LiftProofMode};
use crate::lifter::LiftArch;

/// Loader-derived hints used only for conservative memory region labeling.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct MemoryRegionHints {
    text_base: Option<u64>,
    text_size: Option<u64>,
}

impl MemoryRegionHints {
    #[must_use]
    pub(crate) fn text(text_base: u64, text_size: u64) -> Self {
        Self { text_base: Some(text_base), text_size: Some(text_size) }
    }

    fn text_range(self) -> Option<(u64, u64)> {
        let base = self.text_base?;
        let size = self.text_size?;
        let end = base.checked_add(size)?;
        Some((base, end))
    }

    fn contains_text_addr(self, addr: u64) -> Option<(u64, u64)> {
        let (base, end) = self.text_range()?;
        (addr >= base && addr < end).then_some((base, end - base))
    }
}

/// Local variable layout for a lifted function.
///
/// Maps machine registers, SP, PC, flags, and memory to TrustIr local indices.
/// Public so that downstream crates (e.g. trust_vcgen) can reference layout
/// indices without hardcoding magic constants.
///
/// Architecture-aware: use `LocalLayout::aarch64()` or `LocalLayout::x86_64()`
/// to get the correct register file mapping.
#[derive(Debug, Clone)]
pub struct LocalLayout {
    /// _0: return place
    pub return_local: usize,
    /// Base index of GPR locals (`GPR[i] = gpr_base + i`).
    pub gpr_base: usize,
    /// Number of general-purpose registers in this layout.
    pub gpr_count: usize,
    /// Stack pointer local index.
    pub sp_local: usize,
    /// Program counter local index.
    pub pc_local: usize,
    /// Flag locals — mapped to architecture-specific condition flags.
    /// AArch64: N, Z, C, V. x86_64: CF, ZF, SF, OF.
    pub flag_n: usize,
    pub flag_z: usize,
    pub flag_c: usize,
    pub flag_v: usize,
    /// Memory (array) local index.
    pub mem_local: usize,
    /// Total number of locals.
    pub total: usize,
    /// Human-readable GPR names for `to_local_decls()`.
    gpr_names: GprNames,
    /// Human-readable flag names for `to_local_decls()`.
    flag_names: [&'static str; 4],
}

/// GPR naming strategy — avoids heap allocation for static register names.
#[derive(Debug, Clone)]
enum GprNames {
    /// AArch64: X0..X30 (31 registers).
    Aarch64,
    /// x86_64: RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8-R15 (16 registers).
    X86_64,
}

/// x86_64 GPR names in index order (matching standard register encoding).
const X86_64_GPR_NAMES: [&str; 16] = [
    "RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13",
    "R14", "R15",
];

impl LocalLayout {
    /// AArch64 layout: 0=return, 1-31=X0-X30, 32=SP, 33=PC, 34-37=NZCV, 38=MEM.
    #[must_use]
    pub fn aarch64() -> Self {
        Self {
            return_local: 0,
            gpr_base: 1,
            gpr_count: 31,
            sp_local: 32,
            pc_local: 33,
            flag_n: 34,
            flag_z: 35,
            flag_c: 36,
            flag_v: 37,
            mem_local: 38,
            total: 39,
            gpr_names: GprNames::Aarch64,
            flag_names: ["N", "Z", "C", "V"],
        }
    }

    /// Alias for `aarch64()` — backward compatibility.
    #[must_use]
    pub fn standard() -> Self {
        Self::aarch64()
    }

    /// x86_64 layout: 0=return, 1-16=RAX-R15, 17=RSP, 18=RIP, 19-22=CF/ZF/SF/OF, 23=MEM.
    ///
    /// 16 GPRs (RAX through R15), plus RSP (dedicated stack pointer local),
    /// RIP (program counter), 4 flags (CF/ZF/SF/OF), and MEM. Total: 24.
    #[must_use]
    pub fn x86_64() -> Self {
        Self {
            return_local: 0,
            gpr_base: 1,
            gpr_count: 16,
            sp_local: 17,
            pc_local: 18,
            // x86_64 EFLAGS: CF, ZF, SF, OF
            flag_n: 19,
            flag_z: 20,
            flag_c: 21,
            flag_v: 22,
            mem_local: 23,
            total: 24,
            gpr_names: GprNames::X86_64,
            flag_names: ["CF", "ZF", "SF", "OF"],
        }
    }

    /// Get the local index for a GPR by register index.
    pub(crate) fn gpr(&self, index: u8) -> usize {
        self.gpr_base + index as usize
    }

    /// Build the LocalDecl vector for TrustIr.
    pub(crate) fn to_local_decls(&self) -> Vec<LocalDecl> {
        let mut decls = Vec::with_capacity(self.total);

        // _0: return (u64)
        decls.push(LocalDecl {
            index: 0,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("_lifted_result".to_string()),
        });

        // GPRs
        for i in 0..self.gpr_count {
            let name = match &self.gpr_names {
                GprNames::Aarch64 => format!("X{i}"),
                GprNames::X86_64 => X86_64_GPR_NAMES
                    .get(i)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| format!("GPR{i}")),
            };
            decls.push(LocalDecl {
                index: self.gpr(i as u8),
                ty: Ty::Int { width: 64, signed: false },
                name: Some(name),
            });
        }

        // SP
        decls.push(LocalDecl {
            index: self.sp_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("SP".to_string()),
        });

        // PC
        decls.push(LocalDecl {
            index: self.pc_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("PC".to_string()),
        });

        // Flags
        for (idx, name) in [
            (self.flag_n, self.flag_names[0]),
            (self.flag_z, self.flag_names[1]),
            (self.flag_c, self.flag_names[2]),
            (self.flag_v, self.flag_names[3]),
        ] {
            decls.push(LocalDecl { index: idx, ty: Ty::Bool, name: Some(name.to_string()) });
        }

        // MEM (modeled as u64 for now — semantics are in the formulas)
        decls.push(LocalDecl {
            index: self.mem_local,
            ty: Ty::Int { width: 64, signed: false },
            name: Some("MEM".to_string()),
        });

        decls
    }
}

/// Convert a Formula to a TrustIr Operand.
///
/// Concrete bitvector/boolean constants are lowered to ConstValue for readability;
/// all other formulas become Operand::Symbolic.
fn formula_to_operand(formula: &Formula) -> Operand {
    match formula {
        Formula::BitVec { value, width } => {
            // Non-negative bitvec constants can be represented as ConstValue::Uint.
            if *value >= 0 {
                Operand::Constant(ConstValue::Uint(*value as u128, *width))
            } else {
                Operand::Symbolic(formula.clone())
            }
        }
        Formula::Bool(b) => Operand::Constant(ConstValue::Bool(*b)),
        // Everything else (variables, operations, etc.) is symbolic.
        _ => Operand::Symbolic(formula.clone()),
    }
}

fn unsupported_semantics_error(message: impl Into<String>) -> LiftError {
    LiftError::UnsupportedSemantics { mode: LiftProofMode::SemanticLift, message: message.into() }
}

fn unsupported_effect_error(message: impl Into<String>) -> LiftError {
    LiftError::UnsupportedEffect { mode: LiftProofMode::SemanticLift, message: message.into() }
}

fn instruction_bytes_display(bytes: &[u8]) -> String {
    let bytes = bytes.iter().map(|byte| format!("0x{byte:02x}")).collect::<Vec<_>>().join(", ");
    format!("[{bytes}]")
}

fn instruction_provenance_detail(insn: &Instruction) -> String {
    format!(
        "size {} encoding 0x{:08x} bytes {}",
        insn.size,
        insn.encoding,
        instruction_bytes_display(&insn.bytes)
    )
}

fn unsupported_instruction_semantics_message(
    insn: &Instruction,
    category: &str,
    detail: &str,
    ledger_record: Option<&UnsupportedRecord>,
) -> String {
    let mut message = format!(
        "unsupported instruction semantics at binary:0x{:x} {} opcode {:?}: {category} semantics are unsupported fail-closed ({detail})",
        insn.address,
        instruction_provenance_detail(insn),
        insn.opcode
    );

    if let Some(record) = ledger_record {
        message.push_str(&format!(
            "; unsupported-ledger coverage stage {} feature {:?} opcode {:?} preserves binary origin bytes/opcode",
            record.stage, record.feature, record.opcode
        ));
    }

    message
}

fn unsupported_aarch64_instruction_semantics_error(
    function_entry: Option<u64>,
    insn: &Instruction,
    category: &str,
    detail: &str,
) -> LiftError {
    let ledger = aarch64_fail_closed_proof_boundary_ledger(function_entry, insn);
    let fallback;
    let record = if let Some(record) = ledger.records.first() {
        record
    } else {
        fallback =
            aarch64_fail_closed_proof_boundary_record(function_entry, insn, category, detail);
        &fallback
    };
    unsupported_semantics_error(unsupported_instruction_semantics_message(
        insn,
        category,
        detail,
        Some(record),
    ))
}

fn disasm_register_operand(insn: &Instruction, index: usize) -> Option<String> {
    match insn.operand(index) {
        Some(DisasmOperand::Reg(reg)) => Some(reg.to_string()),
        _ => None,
    }
}

fn disasm_operand_display(operand: &DisasmOperand) -> String {
    match operand {
        DisasmOperand::Reg(reg) => reg.to_string(),
        DisasmOperand::ShiftedReg { reg, shift, amount } => {
            format!("{reg}, {shift} #{amount}")
        }
        DisasmOperand::ExtendedReg { reg, extend, shift } => {
            format!("{reg}, {extend} #{shift}")
        }
        DisasmOperand::Imm(imm) => format!("#{imm}"),
        DisasmOperand::SignedImm(imm) => format!("#{imm}"),
        DisasmOperand::PcRelAddr(addr) => format!("0x{addr:x}"),
        DisasmOperand::Mem(memory) => format!("{memory:?}"),
        DisasmOperand::Cond(cond) => cond.to_string(),
        DisasmOperand::Barrier { domain, kind } => {
            format!("{} {}", aarch64_barrier_domain_name(*domain), aarch64_barrier_type_name(*kind))
        }
        DisasmOperand::SysReg(encoded) => aarch64_system_register_label(*encoded),
        DisasmOperand::BitPos(bit) => format!("#{bit}"),
        _ => format!("{operand:?}"),
    }
}

fn disasm_operand_list_display(insn: &Instruction) -> String {
    let operands = (0..insn.operand_count())
        .filter_map(|index| insn.operand(index).map(disasm_operand_display))
        .collect::<Vec<_>>();

    if operands.is_empty() { "unavailable".to_string() } else { operands.join(", ") }
}

fn sysreg_operand(insn: &Instruction, index: usize) -> Option<u16> {
    match insn.operand(index) {
        Some(DisasmOperand::SysReg(encoded)) => Some(*encoded),
        _ => None,
    }
}

fn aarch64_system_register_label(encoded: u16) -> String {
    let op0 = (encoded >> 14) & 0x3;
    let op1 = (encoded >> 11) & 0x7;
    let crn = (encoded >> 7) & 0xf;
    let crm = (encoded >> 3) & 0xf;
    let op2 = encoded & 0x7;
    let architectural = format!("S{op0}_{op1}_C{crn}_C{crm}_{op2}");

    match encoded {
        0xda10 => format!("NZCV ({architectural}, encoded 0x{encoded:04x})"),
        _ => format!("{architectural} (encoded 0x{encoded:04x})"),
    }
}

fn aarch64_system_register_access_detail(insn: &Instruction) -> String {
    let (action, sysreg_index, gpr_index, preposition) = match insn.opcode {
        Opcode::Mrs => ("MRS reads", 1, 0, "into"),
        Opcode::Msr => ("MSR writes", 0, 1, "from"),
        _ => ("system-register access touches", 0, 1, "with"),
    };
    let sysreg = sysreg_operand(insn, sysreg_index)
        .map(aarch64_system_register_label)
        .unwrap_or_else(|| "unknown system register operand".to_string());
    let gpr = disasm_register_operand(insn, gpr_index)
        .unwrap_or_else(|| "unknown general-purpose register operand".to_string());

    format!(
        "{action} system register {sysreg} {preposition} {gpr}; system register accesses can observe or mutate privileged architectural state outside the scalar model; typed proof blocker: system register bank, privilege level, side effects, exception behavior, and replay witnesses are not modeled; proof-grade lift requires unsupported-ledger coverage and proof-consumed system-register witnesses; status=not proof-consumed; rejecting instead of scalar register lowering"
    )
}

fn aarch64_exception_immediate_detail(insn: &Instruction, mnemonic: &str) -> String {
    match insn.operand(0) {
        Some(DisasmOperand::Imm(imm)) => format!("{mnemonic} exception immediate #{imm}"),
        _ => format!("{mnemonic} exception immediate unavailable"),
    }
}

fn aarch64_trap_blocker_detail(
    insn: &Instruction,
    mnemonic: &str,
    boundary_detail: &str,
) -> String {
    format!(
        "{} {boundary_detail}; typed proof blocker: exception target, handler ABI, privilege transition, architectural side effects, and replay boundary witnesses are not modeled; proof-grade lift requires unsupported-ledger coverage and proof-consumed syscall/trap witnesses; status=not proof-consumed; rejecting instead of fallthrough/no-op lowering",
        aarch64_exception_immediate_detail(insn, mnemonic)
    )
}

fn aarch64_literal_load_blocker_detail(detail: impl AsRef<str>) -> String {
    format!(
        "{}; typed proof blocker: literal-load destination class, PC-relative provenance, relocation/literal-pool bytes, memory snapshot, and replay witnesses are not modeled for this edge case; proof-grade lift requires unsupported-ledger coverage and proof-consumed literal-load witnesses; status=not proof-consumed; rejecting instead of scalar RegWrite/Undef lowering",
        detail.as_ref()
    )
}

fn aarch64_literal_load_semantics_blocker_detail(insn: &Instruction) -> String {
    let detail = match insn.operand(0) {
        Some(DisasmOperand::Reg(dst)) if matches!(dst.kind, RegKind::Gpr | RegKind::Zr) => {
            let width = u32::from(dst.width);
            if !matches!(width, 32 | 64) {
                format!("literal load width {width} is outside the scalar GPR subset")
            } else {
                match insn.operand(1) {
                    Some(DisasmOperand::Mem(DisasmMemoryOperand::PcRelative { offset })) => {
                        format!(
                            "literal load to {dst} ({width}-bit) from PC-relative literal offset {offset}; operands={}",
                            disasm_operand_list_display(insn)
                        )
                    }
                    _ => "expected PC-relative literal operand".to_string(),
                }
            }
        }
        Some(DisasmOperand::Reg(dst)) => {
            format!("literal load destination {dst} uses unsupported register class {:?}", dst.kind)
        }
        _ => "expected scalar destination register for literal load".to_string(),
    };

    aarch64_literal_load_blocker_detail(detail)
}

fn aarch64_fp_simd_load_store_blocker_detail(insn: &Instruction) -> Option<String> {
    if !matches!(insn.opcode, Opcode::Ldr | Opcode::Str) {
        return None;
    }

    let reg = match insn.operand(0) {
        Some(DisasmOperand::Reg(reg)) if reg.kind == RegKind::Simd => *reg,
        _ => return None,
    };
    let memory = match insn.operand(1) {
        Some(DisasmOperand::Mem(memory)) => format!("{memory:?}"),
        _ => "missing memory operand".to_string(),
    };
    let access = if insn.opcode == Opcode::Ldr { "loads into" } else { "stores from" };

    Some(format!(
        "{} {access} FP/SIMD register {reg} ({} bits) through {memory}; typed proof blocker: FP/SIMD register file, vector lane layout, element arrangement, memory byte order, alias/provenance witnesses, and replay witnesses are not modeled by the scalar TrustIr layout; proof-grade lift requires unsupported-ledger coverage and proof-consumed FP/SIMD memory witnesses; status=not proof-consumed; rejecting instead of scalar memory or Undef lowering",
        insn.opcode, reg.width
    ))
}

fn aarch64_fp_simd_compute_family(opcode: Opcode) -> Option<&'static str> {
    match opcode {
        Opcode::Fadd | Opcode::Fsub | Opcode::Fmul | Opcode::Fdiv => Some("aarch64.fp_arithmetic"),
        Opcode::Fabs | Opcode::Fneg | Opcode::Fsqrt => Some("aarch64.fp_unary_arithmetic"),
        Opcode::FmovImm | Opcode::FmovReg => Some("aarch64.fp_move"),
        Opcode::Scvtf | Opcode::Ucvtf | Opcode::Fcvtzs | Opcode::Fcvtzu | Opcode::Fcvt => {
            Some("aarch64.fp_integer_conversion")
        }
        Opcode::Fcsel => Some("aarch64.fp_conditional_select"),
        Opcode::SimdMov => Some("aarch64.simd_move"),
        _ => None,
    }
}

fn aarch64_fp_simd_compute_blocker_detail(insn: &Instruction) -> Option<String> {
    let instruction_family = aarch64_fp_simd_compute_family(insn.opcode)?;
    let operands = disasm_operand_list_display(insn);

    Some(format!(
        "operation={:?}; instruction_family={instruction_family}; operands={operands}; blocker_code=aarch64-fp-simd-compute-not-proof-consumed; typed proof blocker: FP/SIMD register file, vector lane layout, element arrangement, FPCR rounding mode, IEEE-754 flags/exceptions, NaN behavior, scalar-integer conversion semantics, and replay witnesses are not proof-modeled by the scalar TrustIr layout; proof-grade lift requires unsupported-ledger coverage and proof-consumed FP/SIMD compute witnesses; status=not proof-consumed; rejecting instead of scalar or Undef lowering",
        insn.opcode
    ))
}

fn aarch64_non_link_register_return_detail(insn: &Instruction) -> Option<String> {
    if insn.opcode != Opcode::Ret {
        return None;
    }

    match insn.operand(0) {
        Some(DisasmOperand::Reg(reg))
            if reg.kind == RegKind::Gpr && reg.index == 30 && reg.width == 64 =>
        {
            None
        }
        Some(DisasmOperand::Reg(reg)) => Some(format!(
            "RET {reg} is not the ABI link-register return (X30); TrustIr Return has no target-register slot, so proof-grade replay must carry a checked return-target witness and unsupported-ledger coverage for indirect return/call-frame semantics"
        )),
        Some(other) => Some(format!(
            "RET operand {other:?} is not the ABI link-register return (X30); TrustIr Return has no target-register slot, so proof-grade replay must carry a checked return-target witness and unsupported-ledger coverage for indirect return/call-frame semantics"
        )),
        None => Some(
            "RET has no decoded return register; TrustIr Return has no target-register slot, so proof-grade replay must carry a checked return-target witness and unsupported-ledger coverage for indirect return/call-frame semantics"
                .to_string(),
        ),
    }
}

fn aarch64_atomic_ordering_blocker_detail(insn: &Instruction) -> Option<String> {
    let (mnemonic, access, ordering, scalar_data_plane, witnesses, unsound_plain_lowering) =
        match insn.opcode {
            Opcode::Ldar => (
                "LDAR",
                "Load",
                "Acquire",
                "MemRead+RegWrite plus acquire memory ordering",
                "acquire ordering event, synchronization edge, thread identity, happens-before witness",
                "lowering it as a plain load would drop the acquire ordering boundary",
            ),
            Opcode::Stlr => (
                "STLR",
                "Store",
                "Release",
                "MemWrite plus release memory ordering",
                "release ordering event, synchronization edge, thread identity, happens-before witness",
                "lowering it as a plain store would drop the release ordering boundary",
            ),
            _ => return None,
        };

    Some(format!(
        "{mnemonic} memory-order semantics are fail-closed: access={access}; ordering={ordering}; exclusive_monitor=None; reports_status=false; scalar_data_plane={scalar_data_plane}; operands={}; missing witnesses: {witnesses}; proof-consumed witnesses are required before ordered memory effects can be emitted; proof-grade lift requires unsupported-ledger coverage for these witnesses; status=not proof-consumed; {unsound_plain_lowering}",
        disasm_operand_list_display(insn)
    ))
}

fn unsupported_aarch64_semantics_reason(insn: &Instruction) -> Option<(&'static str, String)> {
    if let Some(detail) = aarch64_fp_simd_load_store_blocker_detail(insn) {
        return Some(("AArch64 FP/SIMD load-store", detail));
    }

    match insn.opcode {
        Opcode::FmovImm
        | Opcode::FmovReg
        | Opcode::Fadd
        | Opcode::Fsub
        | Opcode::Fmul
        | Opcode::Fdiv
        | Opcode::Fcsel
        | Opcode::Fabs
        | Opcode::Fneg
        | Opcode::Fsqrt
        | Opcode::Scvtf
        | Opcode::Ucvtf
        | Opcode::Fcvtzs
        | Opcode::Fcvtzu
        | Opcode::Fcvt
        | Opcode::SimdMov => {
            Some(("AArch64 FP/SIMD", aarch64_fp_simd_compute_blocker_detail(insn)?))
        }
        Opcode::Svc => Some((
            "AArch64 syscall/trap",
            aarch64_trap_blocker_detail(
                insn,
                "SVC",
                "can enter the kernel and mutate process state outside the scalar model",
            ),
        )),
        Opcode::Hvc => Some((
            "AArch64 privileged trap",
            aarch64_trap_blocker_detail(
                insn,
                "HVC",
                "can enter a hypervisor and mutate privileged state outside user-mode scalar semantics",
            ),
        )),
        Opcode::Smc => Some((
            "AArch64 privileged trap",
            aarch64_trap_blocker_detail(
                insn,
                "SMC",
                "can enter a secure monitor and mutate privileged state outside user-mode scalar semantics",
            ),
        )),
        Opcode::Brk => Some((
            "AArch64 trap",
            aarch64_trap_blocker_detail(
                insn,
                "BRK",
                "raises a debug exception, a control transfer outside the current CFG model",
            ),
        )),
        Opcode::Hlt => Some((
            "AArch64 trap",
            aarch64_trap_blocker_detail(
                insn,
                "HLT",
                "raises a halt/debug exception, a control transfer outside the current CFG model",
            ),
        )),
        Opcode::LdrLiteral => {
            Some(("AArch64 literal load", aarch64_literal_load_semantics_blocker_detail(insn)))
        }
        Opcode::Mrs | Opcode::Msr => {
            Some(("AArch64 system register", aarch64_system_register_access_detail(insn)))
        }
        Opcode::Wfe => Some((
            "AArch64 system wait/hint",
            "WFE can wait on event state; typed proof blocker: event register state, scheduler/thread identity, wakeup/invalidation conditions, and proof-grade witnesses are not modeled; treating it as a scalar no-op would drop the wait/synchronization boundary"
                .to_string(),
        )),
        Opcode::Wfi => Some((
            "AArch64 system wait/hint",
            "WFI can wait on interrupt state; typed proof blocker: interrupt mask/state, scheduler/thread identity, wakeup conditions, and proof-grade witnesses are not modeled; treating it as a scalar no-op would drop the wait/synchronization boundary"
                .to_string(),
        )),
        Opcode::Ret => aarch64_non_link_register_return_detail(insn)
            .map(|detail| ("AArch64 indirect return boundary", detail)),
        Opcode::Ldar | Opcode::Stlr => Some((
            "AArch64 atomic memory-order",
            aarch64_atomic_ordering_blocker_detail(insn)?,
        )),
        Opcode::Ldxr | Opcode::Stxr | Opcode::Ldaxr | Opcode::Stlxr => Some((
            "AArch64 atomic/exclusive memory-order",
            aarch64_exclusive_monitor_blocker_detail(insn.opcode)?,
        )),
        _ => None,
    }
}

fn aarch64_exclusive_monitor_blocker_detail(opcode: Opcode) -> Option<String> {
    let (
        mnemonic,
        access,
        ordering,
        monitor_operation,
        reports_status,
        scalar_data_plane,
        witnesses,
        unsound_plain_lowering,
    ) = match opcode {
        Opcode::Ldxr => (
            "LDXR",
            "Load",
            "Relaxed",
            "LoadReserve",
            false,
            "MemRead+RegWrite plus monitor reservation",
            "monitor reservation state, monitor invalidation, thread identity",
            "lowering it as a plain load would drop the exclusive monitor reservation",
        ),
        Opcode::Stxr => (
            "STXR",
            "Store",
            "Relaxed",
            "StoreConditional",
            true,
            "conditional MemWrite plus status RegWrite",
            "monitor reservation state, monitor invalidation, thread identity, store-conditional status result",
            "lowering it as an unconditional store would be unsound because STXR conditionally stores and reports success",
        ),
        Opcode::Ldaxr => (
            "LDAXR",
            "Load",
            "Acquire",
            "LoadReserve",
            false,
            "MemRead+RegWrite plus acquire memory ordering plus monitor reservation",
            "acquire ordering event, synchronization edge, monitor reservation state, monitor invalidation, thread identity, happens-before witness",
            "lowering it as a plain acquire load would drop the exclusive monitor reservation",
        ),
        Opcode::Stlxr => (
            "STLXR",
            "Store",
            "Release",
            "StoreConditional",
            true,
            "conditional MemWrite plus release memory ordering plus status RegWrite",
            "release ordering event, synchronization edge, monitor reservation state, monitor invalidation, thread identity, store-conditional status result, happens-before witness",
            "lowering it as a plain release store would drop both the monitor condition and the status result",
        ),
        _ => return None,
    };

    Some(format!(
        "{mnemonic} exclusive monitor semantics are fail-closed: access={access}; ordering={ordering}; monitor_operation={monitor_operation}; reports_status={reports_status}; scalar_data_plane={scalar_data_plane}; missing witnesses: {witnesses}; proof-consumed witnesses are required before monitor effects can be emitted; proof-grade lift requires unsupported-ledger coverage for these witnesses; {unsound_plain_lowering}"
    ))
}

fn aarch64_fail_closed_proof_boundary_record(
    function_entry: Option<u64>,
    insn: &Instruction,
    category: &str,
    detail: &str,
) -> UnsupportedRecord {
    unsupported_aarch64_semantics_record(function_entry, LiftArch::Aarch64, insn, category, detail)
}

fn aarch64_fail_closed_proof_boundary_ledger(
    function_entry: Option<u64>,
    insn: &Instruction,
) -> UnsupportedLedger {
    let mut unsupported = UnsupportedLedger::default();
    if let Some((category, detail)) = unsupported_aarch64_semantics_reason(insn) {
        unsupported.records.push(aarch64_fail_closed_proof_boundary_record(
            function_entry,
            insn,
            category,
            &detail,
        ));
    }
    unsupported
}

#[cfg(test)]
fn aarch64_empty_unsupported_ledger_boundary(insn: &Instruction) -> Option<&'static str> {
    match insn.opcode {
        Opcode::Nop => Some(
            "exact-empty-ledger-boundary:aarch64.nop; no scalar, memory, ordering, monitor, ABI, or CFG side effect beyond proof-bound PC provenance",
        ),
        Opcode::Yield | Opcode::Sev | Opcode::Sevl => Some(
            "exact-empty-ledger-boundary:aarch64.local-hint; accepted only as a local no-data hint; WFE/WFI wait semantics remain outside this boundary",
        ),
        Opcode::Prfm => Some(
            "exact-empty-ledger-boundary:aarch64.prefetch-hint; no memory read/write fact is emitted and cache effects are outside the scalar proof claim",
        ),
        Opcode::Ret if aarch64_non_link_register_return_detail(insn).is_none() => Some(
            "exact-empty-ledger-boundary:aarch64.ret-x30; accepted only for ABI link-register return represented by a TrustIr Return terminator",
        ),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Aarch64AcceptedOrderingRole {
    Release,
    Acquire,
}

const AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA: &str =
    "trust-lift.aarch64.release_acquire_ordering_evidence@1";
const AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX: &str = "aarch64-ra:sha256:";
const AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA: &str =
    "trust-lift.aarch64.ordering_monitor_evidence_row@1";
const AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE: &str = "aarch64_ordering_monitor_evidence";
const AARCH64_REVIEWED_UNSUPPORTED_ABSENCE: &str = "[barrier absent-reviewed, exclusive-monitor absent-reviewed, store-conditional-status absent-reviewed, system-register absent-reviewed, FP/SIMD absent-reviewed, trap absent-reviewed, syscall absent-reviewed, unsupported-opcode absent-reviewed]";

impl Aarch64AcceptedOrderingRole {
    fn label(self) -> &'static str {
        match self {
            Self::Release => "release",
            Self::Acquire => "acquire",
        }
    }

    fn ordering_event(self) -> &'static str {
        match self {
            Self::Release => "release ordering event",
            Self::Acquire => "acquire ordering event",
        }
    }

    fn opcode(self) -> &'static str {
        match self {
            Self::Release => "Stlr",
            Self::Acquire => "Ldar",
        }
    }

    fn ordering(self) -> &'static str {
        match self {
            Self::Release => "Release",
            Self::Acquire => "Acquire",
        }
    }
}

fn aarch64_accepted_release_acquire_slice_role(
    block: &LiftedBlock,
    insn_index: usize,
) -> Option<Aarch64AcceptedOrderingRole> {
    if !block.is_return || block.instructions.len() != 3 {
        return None;
    }

    let release = &block.instructions[0];
    let acquire = &block.instructions[1];
    let ret = &block.instructions[2];
    if release.opcode != Opcode::Stlr
        || acquire.opcode != Opcode::Ldar
        || aarch64_non_link_register_return_detail(ret).is_some()
    {
        return None;
    }

    let release_mem = aarch64_memory_operand_identity(release)?;
    if Some(release_mem.as_str()) != aarch64_memory_operand_identity(acquire).as_deref() {
        return None;
    }
    if aarch64_atomic_register_width(release)? != aarch64_atomic_register_width(acquire)? {
        return None;
    }

    match insn_index {
        0 => Some(Aarch64AcceptedOrderingRole::Release),
        1 => Some(Aarch64AcceptedOrderingRole::Acquire),
        _ => None,
    }
}

fn aarch64_memory_operand_identity(insn: &Instruction) -> Option<String> {
    insn.operands().find_map(|operand| {
        if let DisasmOperand::Mem(mem) = operand { Some(format!("{mem:?}")) } else { None }
    })
}

fn aarch64_atomic_register_width(insn: &Instruction) -> Option<u16> {
    match insn.operand(0) {
        Some(DisasmOperand::Reg(reg)) if reg.kind == RegKind::Gpr => Some(reg.width),
        _ => None,
    }
}

fn aarch64_release_acquire_selected_image_digest(
    function_entry: u64,
    block: &LiftedBlock,
) -> String {
    let release_origin = binary_origin_for_instruction(function_entry, &block.instructions[0]);
    let acquire_origin = binary_origin_for_instruction(function_entry, &block.instructions[1]);
    stable_sha256_hex(
        aarch64_release_acquire_selected_image_material(
            function_entry,
            &release_origin,
            &acquire_origin,
        )
        .as_bytes(),
    )
}

fn aarch64_release_acquire_selected_image_material(
    function_entry: u64,
    release_origin: &BinaryOrigin,
    acquire_origin: &BinaryOrigin,
) -> String {
    format!(
        "schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}\n\
         boundary=aarch64.release_acquire\n\
         selected_image_identity=function_entry=0x{function_entry:x},release=0x{:x}/0x{},acquire=0x{:x}/0x{}\n\
         release_origin={}\n\
         acquire_origin={}\n\
         unsupported_ledger_boundary=explicit-empty\n\
         unsupported_ledger_records=0",
        release_origin.instruction_address,
        aarch64_optional_encoding(release_origin.encoding),
        acquire_origin.instruction_address,
        aarch64_optional_encoding(acquire_origin.encoding),
        aarch64_binary_origin_material(release_origin),
        aarch64_binary_origin_material(acquire_origin),
    )
}

fn aarch64_optional_encoding(encoding: Option<u32>) -> String {
    encoding.map_or_else(|| "unavailable".to_string(), |encoding| format!("{encoding:08x}"))
}

fn aarch64_binary_origin_material(origin: &BinaryOrigin) -> String {
    format!(
        "binary_path={};function_entry={};instruction_address=0x{:x};instruction_size={};encoding={};instruction_bytes={}",
        origin.binary_path.as_deref().unwrap_or("<unavailable>"),
        origin
            .function_entry
            .map_or_else(|| "<unavailable>".to_string(), |entry| format!("0x{entry:x}")),
        origin.instruction_address,
        origin
            .instruction_size
            .map_or_else(|| "<unavailable>".to_string(), |size| size.to_string()),
        origin
            .encoding
            .map_or_else(|| "<unavailable>".to_string(), |encoding| format!("0x{encoding:08x}")),
        instruction_bytes_display(&origin.instruction_bytes),
    )
}

fn aarch64_memory_access_material(fact: &MemoryAccessFact) -> String {
    let mut taint = fact.taint.clone();
    taint.sort();
    format!(
        "origin={};kind={:?};address={:?};width_bytes={};endianness={:?};region={:?};base_object={};offset={:?};extent={};taint=[{}]",
        aarch64_binary_origin_material(&fact.origin),
        fact.kind,
        fact.address,
        fact.width_bytes,
        fact.endianness,
        fact.region,
        fact.base_object.as_deref().unwrap_or("<none>"),
        fact.offset,
        fact.extent.map_or_else(|| "<none>".to_string(), |extent| extent.to_string()),
        taint.join(","),
    )
}

fn aarch64_instruction_provenance_digest(origin: &BinaryOrigin) -> String {
    stable_sha256_hex(aarch64_binary_origin_material(origin).as_bytes())
}

fn aarch64_memory_access_digest(fact: &MemoryAccessFact) -> String {
    stable_sha256_hex(aarch64_memory_access_material(fact).as_bytes())
}

fn aarch64_release_acquire_evidence_hash(
    role: Aarch64AcceptedOrderingRole,
    selected_image_digest: &str,
    instruction_provenance_digest: &str,
    memory_access_digest: &str,
) -> String {
    stable_sha256_hex(
        format!(
            "schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}\n\
             boundary=aarch64.release_acquire\n\
             artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}\n\
             artifact_row_type={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE}\n\
             artifact_row_status=accepted\n\
             role={}\n\
             opcode={}\n\
             ordering={}\n\
             exclusive_monitor=None\n\
             exclusive_monitor_witness=not-applicable-reviewed\n\
             store_conditional_status=not-applicable-reviewed\n\
             ordering_event={}\n\
             synchronization_edge=absent-reviewed\n\
             happens_before_witness=absent-reviewed\n\
             thread_identity=absent-reviewed\n\
             selected_image_digest=sha256:{selected_image_digest}\n\
             instruction_provenance_digest=sha256:{instruction_provenance_digest}\n\
             memory_access_digest=sha256:{memory_access_digest}\n\
             unsupported_ledger_boundary=explicit-empty\n\
             unsupported_ledger_records=0\n\
             reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}\n\
             consumed_witnesses=[{}, same atomic location witness]\n\
             aarch64_ordering_monitor_evidence_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}\n\
             aarch64_ordering_monitor_evidence_status=accepted\n\
             aarch64_ordering_monitor_evidence_opcode={}\n\
             aarch64_ordering_monitor_evidence_ordering={}\n\
             aarch64_ordering_monitor_evidence_exclusive_monitor=None\n\
             aarch64_ordering_monitor_evidence_blockers=[]\n\
             release_transcript_consumed=true",
            role.label(),
            role.opcode(),
            role.ordering(),
            role.ordering_event(),
            role.ordering_event(),
            role.opcode(),
            role.ordering(),
        )
        .as_bytes(),
    )
}

fn aarch64_release_acquire_evidence_id(
    role: Aarch64AcceptedOrderingRole,
    selected_image_digest: &str,
    instruction_provenance_digest: &str,
    memory_access_digest: &str,
) -> String {
    format!(
        "{AARCH64_RELEASE_ACQUIRE_EVIDENCE_ID_PREFIX}{}",
        aarch64_release_acquire_evidence_hash(
            role,
            selected_image_digest,
            instruction_provenance_digest,
            memory_access_digest,
        )
    )
}

fn aarch64_accepted_ordering_provenance(
    function_entry: u64,
    block: &LiftedBlock,
    fact: &MemoryAccessFact,
    role: Aarch64AcceptedOrderingRole,
) -> String {
    let selected_image_digest =
        aarch64_release_acquire_selected_image_digest(function_entry, block);
    let instruction_digest = aarch64_instruction_provenance_digest(&fact.origin);
    let memory_digest = aarch64_memory_access_digest(fact);
    let evidence_hash = aarch64_release_acquire_evidence_hash(
        role,
        &selected_image_digest,
        &instruction_digest,
        &memory_digest,
    );
    let evidence_id = aarch64_release_acquire_evidence_id(
        role,
        &selected_image_digest,
        &instruction_digest,
        &memory_digest,
    );

    format!(
        "accepted-slice:aarch64.release_acquire; role={}; status=proof-consumed; evidence_schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}; evidence_id={evidence_id}; artifact_digest=sha256:{evidence_hash}; artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}; artifact_row_type={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE}; artifact_row_status=accepted; selected_image_identity=function_entry=0x{function_entry:x},release=0x{:x}/0x{},acquire=0x{:x}/0x{}; selected_image_digest=sha256:{selected_image_digest}; instruction_provenance_digest=sha256:{instruction_digest}; memory_access_digest=sha256:{memory_digest}; opcode={}; ordering={}; ordering_event={}; exclusive_monitor=None; exclusive_monitor_witness=not-applicable-reviewed; store_conditional_status=not-applicable-reviewed; synchronization_edge=absent-reviewed; happens_before_witness=absent-reviewed; thread_identity=absent-reviewed; unsupported_ledger_boundary=explicit-empty; unsupported_ledger_records=0; reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}; consumed_witnesses=[{}, same atomic location witness]; reviewed_absence=[exclusive_monitor=None, exclusive monitor absent-reviewed, store-conditional status not-applicable-reviewed, synchronization edge absent-reviewed, happens-before witness absent-reviewed, thread identity absent-reviewed]; aarch64_ordering_monitor_evidence_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}; aarch64_ordering_monitor_evidence_status=accepted; aarch64_ordering_monitor_evidence_opcode={}; aarch64_ordering_monitor_evidence_ordering={}; aarch64_ordering_monitor_evidence_exclusive_monitor=None; aarch64_ordering_monitor_evidence_digest=sha256:{evidence_hash}; aarch64_ordering_monitor_evidence_blockers=[]; release_transcript_consumed=true; release_transcript_digest=sha256:{evidence_hash}; no FP/SIMD/syscall/trap/exception claim; no exclusive-monitor/status claim",
        role.label(),
        block.instructions[0].address,
        aarch64_optional_encoding(Some(block.instructions[0].encoding)),
        block.instructions[1].address,
        aarch64_optional_encoding(Some(block.instructions[1].encoding)),
        role.opcode(),
        role.ordering(),
        role.ordering_event(),
        role.ordering_event(),
        role.opcode(),
        role.ordering(),
    )
}

fn annotate_aarch64_accepted_ordering_access(
    fact: &mut MemoryAccessFact,
    function_entry: u64,
    block: &LiftedBlock,
    role: Aarch64AcceptedOrderingRole,
) {
    let certificate = aarch64_accepted_ordering_provenance(function_entry, block, fact, role);
    fact.provenance = Some(match fact.provenance.take() {
        Some(existing) if !existing.is_empty() => format!("{existing}; {certificate}"),
        _ => certificate,
    });
}

fn x86_64_empty_unsupported_ledger_boundary(insn: &Instruction) -> Option<&'static str> {
    match insn.opcode {
        Opcode::Nop => Some(
            "exact-empty-ledger-boundary:x86_64.nop; accepted only as a selected no-data slice instruction with PC provenance; no memory, flag, stack, ABI, syscall, or security claim is made",
        ),
        Opcode::Endbr64 => Some(
            "exact-empty-ledger-boundary:x86_64.endbr64; accepted only as a selected CET landing-pad marker; indirect-branch validation remains outside this empty-ledger claim",
        ),
        _ => None,
    }
}

fn unsupported_x86_64_semantics_reason(insn: &Instruction) -> Option<(&'static str, String)> {
    let operands = disasm_operand_list_display(insn);
    match insn.opcode {
        Opcode::Syscall => Some((
            "x86_64 syscall boundary",
            format!(
                "SYSCALL operands={operands}; typed proof blocker: kernel entry ABI, privilege transition, clobbered registers, memory side effects, errno/signal behavior, and replay witnesses are not modeled; proof-grade lift requires unsupported-ledger coverage and proof-consumed syscall/ABI witnesses; status=not proof-consumed; rejecting instead of fallthrough/no-op lowering"
            ),
        )),
        Opcode::Int3 => Some((
            "x86_64 trap boundary",
            format!(
                "INT3 operands={operands}; typed proof blocker: exception target, debugger/trap handler ABI, architectural side effects, and replay boundary witnesses are not modeled; proof-grade lift requires unsupported-ledger coverage and proof-consumed trap witnesses; status=not proof-consumed; rejecting instead of fallthrough/no-op lowering"
            ),
        )),
        Opcode::Call => Some((
            "x86_64 call ABI boundary",
            format!(
                "CALL operands={operands}; typed proof blocker: callee summary, SysV register/stack ABI effects, return-address stack write, unwind/security side conditions, and replay call-target witnesses are not proof-consumed; proof-grade lift requires unsupported-ledger coverage and callee-summary witnesses; status=not proof-consumed; rejecting instead of inlining an unconstrained call"
            ),
        )),
        _ => None,
    }
}

fn x86_64_fail_closed_proof_boundary_record(
    function_entry: Option<u64>,
    insn: &Instruction,
    category: &str,
    detail: &str,
) -> UnsupportedRecord {
    unsupported_record_for_instruction(
        "trust-lift::semantic-lift",
        format!("{category} semantics are unsupported fail-closed: {detail}"),
        function_entry,
        LiftArch::X86_64,
        insn,
    )
}

fn x86_64_fail_closed_proof_boundary_ledger(
    function_entry: Option<u64>,
    insn: &Instruction,
) -> UnsupportedLedger {
    let mut unsupported = UnsupportedLedger::default();
    if let Some((category, detail)) = unsupported_x86_64_semantics_reason(insn) {
        unsupported.records.push(x86_64_fail_closed_proof_boundary_record(
            function_entry,
            insn,
            category,
            &detail,
        ));
    }
    unsupported
}

fn unsupported_x86_64_instruction_semantics_error(
    function_entry: Option<u64>,
    insn: &Instruction,
    category: &str,
    detail: &str,
) -> LiftError {
    let ledger = x86_64_fail_closed_proof_boundary_ledger(function_entry, insn);
    let fallback;
    let record = if let Some(record) = ledger.records.first() {
        record
    } else {
        fallback = x86_64_fail_closed_proof_boundary_record(function_entry, insn, category, detail);
        &fallback
    };
    unsupported_semantics_error(unsupported_instruction_semantics_message(
        insn,
        category,
        detail,
        Some(record),
    ))
}

fn modeled_partial_x86_64_semantic_feature(insn: &Instruction) -> Option<String> {
    if x86_64_empty_unsupported_ledger_boundary(insn).is_some() {
        return None;
    }

    let operands = disasm_operand_list_display(insn);
    let feature = match insn.opcode {
        Opcode::Ret => format!(
            "x86_64 ABI return boundary outside exact empty-ledger release slice; operands={operands}; typed proof blocker: return-target stack read, canonical frame/stack restoration, red-zone/unwind constraints, and saved-return-address security witnesses are not proof-consumed; security/ABI VCs remain blockers"
        ),
        Opcode::Push | Opcode::Pop | Opcode::Leave => format!(
            "x86_64 stack/ABI data movement outside exact empty-ledger release slice; opcode {:?}; operands={operands}; typed proof blocker: stack object bounds, frame layout, alias/provenance, red-zone, and saved-return-address overwrite witnesses are not proof-consumed",
            insn.opcode
        ),
        Opcode::Jmp | Opcode::Jcc => format!(
            "x86_64 control-flow boundary outside exact empty-ledger release slice; opcode {:?}; operands={operands}; typed proof blocker: target identity, CFG recovery, fallthrough/branch witnesses, and indirect-target security classification are not proof-consumed",
            insn.opcode
        ),
        Opcode::Mov
        | Opcode::Lea
        | Opcode::Add
        | Opcode::Sub
        | Opcode::Cmp
        | Opcode::Test
        | Opcode::Xor
        | Opcode::Or
        | Opcode::Inc
        | Opcode::Dec
        | Opcode::Neg
        | Opcode::Not
        | Opcode::Shl
        | Opcode::Shr
        | Opcode::Sar
        | Opcode::Imul
        | Opcode::Mul
        | Opcode::Div
        | Opcode::Idiv
        | Opcode::Movzx
        | Opcode::Movsx
        | Opcode::Movsxd
        | Opcode::Cdq
        | Opcode::Cqo
        | Opcode::Xchg
        | Opcode::Cmovcc
        | Opcode::Setcc
        | Opcode::Cmpxchg
        | Opcode::Bsf
        | Opcode::Bsr => format!(
            "x86_64 scalar/data instruction outside exact empty-ledger release slice; opcode {:?}; operands={operands}; typed proof blocker: operand-width normalization, flag side effects, memory addressing/provenance, and replay witnesses are not part of the narrow no-data empty-ledger claim",
            insn.opcode
        ),
        _ => return None,
    };

    Some(feature)
}

fn machine_semantics_error(
    arch: LiftArch,
    function_entry: Option<u64>,
    insn: &Instruction,
    err: SemError,
) -> LiftError {
    match (arch, err) {
        (LiftArch::X86_64, SemError::UnsupportedOpcode(_)) => {
            unsupported_x86_64_instruction_semantics_error(
                function_entry,
                insn,
                "x86_64 ISA opcode",
                &format!(
                    "opcode {:?} is decoded but outside the modeled x86_64 proof subset; typed proof blocker: instruction semantics, flag/memory side effects, and replay witnesses are not proof-consumed",
                    insn.opcode
                ),
            )
        }
        (_, err) => unsupported_semantics_error(format!(
            "unsupported instruction semantics at binary:0x{:x} {} opcode {:?}: {err}",
            insn.address,
            instruction_provenance_detail(insn),
            insn.opcode
        )),
    }
}

fn modeled_partial_aarch64_semantic_feature(insn: &Instruction) -> Option<&'static str> {
    match insn.opcode {
        Opcode::Fcmp => Some(
            "AArch64 FP compare modeled as partial flag boundary; unsupported-ledger boundary status=not proof-consumed until IEEE-754 comparison, FPCR, NaN/unordered, and FP register witnesses are proof-consumed; scalar flag TrustIr is emitted with this ledger record instead of silent scalar/Undef lowering",
        ),
        _ => None,
    }
}

fn aarch64_barrier_operand_detail(insn: &Instruction) -> Option<String> {
    match insn.operand(0) {
        Some(DisasmOperand::Barrier { domain, kind }) => Some(format!(
            "{} {}",
            aarch64_barrier_domain_name(*domain),
            aarch64_barrier_type_name(*kind)
        )),
        _ => None,
    }
}

fn aarch64_barrier_domain_name(domain: BarrierDomain) -> &'static str {
    match domain {
        BarrierDomain::Osh => "OSH",
        BarrierDomain::Nsh => "NSH",
        BarrierDomain::Ish => "ISH",
        BarrierDomain::Sy => "SY",
        _ => "unknown",
    }
}

fn aarch64_barrier_type_name(kind: BarrierType) -> &'static str {
    match kind {
        BarrierType::Ld => "load",
        BarrierType::St => "store",
        BarrierType::Full => "full",
        _ => "unknown",
    }
}

fn unresolved_control_flow_error(message: impl Into<String>) -> LiftError {
    LiftError::UnresolvedControlFlow { mode: LiftProofMode::SemanticLift, message: message.into() }
}

fn missing_successor_error(message: impl Into<String>) -> LiftError {
    LiftError::MissingSuccessor { mode: LiftProofMode::SemanticLift, message: message.into() }
}

fn unrepresentable_cfg_error(message: impl Into<String>) -> LiftError {
    LiftError::UnrepresentableCfg { mode: LiftProofMode::SemanticLift, message: message.into() }
}

/// Convert a single Effect into TrustIr Statement(s).
///
/// # Trust: #564 — uses actual Formula values from Effects
///
/// Each Effect variant carries Formula fields describing the actual computation.
/// We emit those into TrustIr via `Operand::Symbolic(formula)` so downstream VC
/// generation reasons over real semantics, not placeholders.
fn effect_to_stmts(
    effect: &Effect,
    layout: &LocalLayout,
    binary_addr: u64,
) -> Result<Vec<Statement>, LiftError> {
    let span = SourceSpan::binary_address(binary_addr);

    match effect {
        Effect::RegWrite { index, value, .. } => {
            // Trust: #573 — architecture-aware GPR bounds.
            // AArch64: index 31 is ZR (writes are no-ops).
            // x86_64: all 16 GPR indices (0-15) are real registers.
            if (*index as usize) >= layout.gpr_count {
                return Ok(vec![Statement::Nop]);
            }
            // Trust: #564 — emit actual formula value, not placeholder zero.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.gpr(*index)),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::SpWrite { value } => {
            // Trust: #564 — emit actual SP formula.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.sp_local),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::MemWrite { address, value, width_bytes } => {
            let store_formula = byte_store_formula(mem_formula(), address, value, *width_bytes);
            Ok(vec![Statement::Assign {
                place: Place::local(layout.mem_local),
                rvalue: Rvalue::Use(Operand::Symbolic(store_formula)),
                span,
            }])
        }
        Effect::MemRead { .. } => {
            // Memory reads are modeled as part of the subsequent RegWrite
            Ok(vec![Statement::Nop])
        }
        Effect::FlagUpdate { n, z, c, v } => {
            // Trust: #564 — emit actual flag formulas, not placeholder false.
            Ok(vec![
                Statement::Assign {
                    place: Place::local(layout.flag_n),
                    rvalue: Rvalue::Use(formula_to_operand(n)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_z),
                    rvalue: Rvalue::Use(formula_to_operand(z)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_c),
                    rvalue: Rvalue::Use(formula_to_operand(c)),
                    span: span.clone(),
                },
                Statement::Assign {
                    place: Place::local(layout.flag_v),
                    rvalue: Rvalue::Use(formula_to_operand(v)),
                    span,
                },
            ])
        }
        Effect::Branch { .. } | Effect::ConditionalBranch { .. } => {
            // Branches are handled at the terminator level, not as statements
            Ok(vec![])
        }
        Effect::Call { target, .. } => Err(unsupported_effect_error(format!(
            "unsupported call effect at binary:0x{binary_addr:x}: target {target:?}; no callee summary is available"
        ))),
        Effect::Return { .. } => {
            // Returns are handled at the terminator level
            Ok(vec![])
        }
        Effect::PcUpdate { value } => {
            // Trust: #564 — emit actual PC formula.
            Ok(vec![Statement::Assign {
                place: Place::local(layout.pc_local),
                rvalue: Rvalue::Use(formula_to_operand(value)),
                span,
            }])
        }
        Effect::Aarch64SyncBoundary { .. } => {
            // Synchronization boundaries are recorded in the unsupported ledger
            // by the lifting loop. They do not mutate scalar TrustIr data state.
            Ok(vec![Statement::Nop])
        }
        Effect::Aarch64AtomicAccess { .. } => {
            // Per-access atomic ordering metadata is recorded in the
            // unsupported ledger. The scalar data plane is carried by the
            // adjacent MemRead/RegWrite or MemWrite effects.
            Ok(vec![Statement::Nop])
        }
        Effect::FpRegWrite { index, width, .. } => Err(unsupported_effect_error(format!(
            "unsupported FP register write effect at binary:0x{binary_addr:x}: V{index} width {width}; no TrustIr FP local layout is available"
        ))),
        _ => Err(unsupported_effect_error(format!(
            "unsupported effect at binary:0x{binary_addr:x}: {effect:?}"
        ))),
    }
}

fn mem_formula() -> Formula {
    Formula::Var(
        "MEM".into(),
        trust_types::Sort::Array(
            Box::new(trust_types::Sort::BitVec(64)),
            Box::new(trust_types::Sort::BitVec(8)),
        ),
    )
}

fn byte_store_formula(
    memory: Formula,
    address: &Formula,
    value: &Formula,
    width_bytes: u32,
) -> Formula {
    let mut current = memory;
    for byte_index in 0..width_bytes {
        let byte_address = if byte_index == 0 {
            address.clone()
        } else {
            Formula::BvAdd(
                Box::new(address.clone()),
                Box::new(Formula::BitVec { value: i128::from(byte_index), width: 64 }),
                64,
            )
        };
        let byte_value = Formula::BvExtract {
            inner: Box::new(value.clone()),
            high: byte_index * 8 + 7,
            low: byte_index * 8,
        };
        current = Formula::Store(Box::new(current), Box::new(byte_address), Box::new(byte_value));
    }
    current
}

fn byte_load_formula(
    memory: &Formula,
    address: &Formula,
    width_bytes: u32,
    result_width: u32,
) -> Formula {
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for byte_index in 0..width_bytes {
        let byte_address = if byte_index == 0 {
            address.clone()
        } else {
            Formula::BvAdd(
                Box::new(address.clone()),
                Box::new(Formula::BitVec { value: i128::from(byte_index), width: 64 }),
                64,
            )
        };
        let byte_value = Formula::Select(Box::new(memory.clone()), Box::new(byte_address));
        let extended = Formula::BvZeroExt(Box::new(byte_value), result_width);
        if byte_index == 0 {
            result = extended;
        } else {
            let shift_amount =
                Formula::BitVec { value: i128::from(byte_index * 8), width: result_width };
            let shifted = Formula::BvShl(Box::new(extended), Box::new(shift_amount), result_width);
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        }
    }
    result
}

fn successor_block_id(
    cfg: &Cfg,
    block: &LiftedBlock,
    successor_addr: u64,
    ordinal: usize,
) -> Result<BlockId, LiftError> {
    cfg.block_index(successor_addr)
        .map(BlockId)
        .ok_or_else(|| {
            missing_successor_error(format!(
                "block {} at 0x{:x} successor #{ordinal} points to 0x{successor_addr:x}, which is not a recovered block",
                block.id, block.start_addr
            ))
        })
}

fn bitvec_mask(width: u32) -> Option<u128> {
    match width {
        0 => None,
        64 => Some(u128::from(u64::MAX)),
        1..=63 => Some((1u128 << width) - 1),
        _ => None,
    }
}

fn bitvec_value_to_u64(value: i128, width: u32) -> Option<u64> {
    let mask = bitvec_mask(width)?;
    let modulus = mask + 1;
    let normalized = if value < 0 {
        let modulus = i128::try_from(modulus).ok()?;
        value.rem_euclid(modulus) as u128
    } else {
        u128::try_from(value).ok()?
    };

    if normalized <= mask { u64::try_from(normalized).ok() } else { None }
}

fn constant_pc_value(formula: &Formula) -> Option<u64> {
    match formula {
        Formula::BitVec { value, width } => bitvec_value_to_u64(*value, *width),
        Formula::UInt(value) => u64::try_from(*value).ok(),
        Formula::Int(value) => u64::try_from(*value).ok(),
        Formula::BvAdd(lhs, rhs, width) => {
            let mask = bitvec_mask(*width)?;
            let lhs = u128::from(constant_pc_value(lhs)?);
            let rhs = u128::from(constant_pc_value(rhs)?);
            u64::try_from((lhs.wrapping_add(rhs)) & mask).ok()
        }
        Formula::BvSub(lhs, rhs, width) => {
            let mask = bitvec_mask(*width)?;
            let lhs = u128::from(constant_pc_value(lhs)?);
            let rhs = u128::from(constant_pc_value(rhs)?);
            u64::try_from((lhs.wrapping_sub(rhs)) & mask).ok()
        }
        Formula::BvZeroExt(inner, width) => {
            let mask = bitvec_mask(*width)?;
            u64::try_from(u128::from(constant_pc_value(inner)?) & mask).ok()
        }
        Formula::IntToBv(inner, width) => {
            let value = match inner.as_ref() {
                Formula::Int(value) => *value,
                Formula::UInt(value) => i128::try_from(*value).ok()?,
                Formula::BitVec { value, .. } => *value,
                _ => return None,
            };
            bitvec_value_to_u64(value, *width)
        }
        _ => None,
    }
}

fn branch_discr_from_final_pc_update(
    block: &LiftedBlock,
    value: &Formula,
    target_addr: u64,
    fallthrough_addr: u64,
) -> Result<Operand, LiftError> {
    let Formula::Ite(condition, target, fallthrough) = value else {
        return Err(unresolved_control_flow_error(format!(
            "block {} at 0x{:x} has two CFG successors but no conditional branch semantics",
            block.id, block.start_addr
        )));
    };

    let actual_target = constant_pc_value(target).ok_or_else(|| {
        unresolved_control_flow_error(format!(
            "block {} at 0x{:x} final PC ITE target is not a constant address: {target:?}",
            block.id, block.start_addr
        ))
    })?;
    let actual_fallthrough = constant_pc_value(fallthrough).ok_or_else(|| {
        unresolved_control_flow_error(format!(
            "block {} at 0x{:x} final PC ITE fallthrough is not a constant address: {fallthrough:?}",
            block.id, block.start_addr
        ))
    })?;

    if actual_target != target_addr || actual_fallthrough != fallthrough_addr {
        return Err(unresolved_control_flow_error(format!(
            "block {} at 0x{:x} final PC ITE destinations do not match recovered CFG: target 0x{actual_target:x} vs 0x{target_addr:x}, fallthrough 0x{actual_fallthrough:x} vs 0x{fallthrough_addr:x}",
            block.id, block.start_addr
        )));
    }

    Ok(Operand::Symbolic(condition.as_ref().clone()))
}

fn conditional_branch_discr(
    block: &LiftedBlock,
    effects_for_block: &[Effect],
    state: &MachineState,
    target_addr: u64,
    fallthrough_addr: u64,
) -> Result<Operand, LiftError> {
    if let Some(discr) = effects_for_block.iter().rev().find_map(|eff| {
        if let Effect::ConditionalBranch { condition, .. } = eff {
            Some(Operand::Symbolic(trust_machine_sem::condition_to_formula(state, *condition)))
        } else {
            None
        }
    }) {
        return Ok(discr);
    }

    match effects_for_block.last() {
        Some(Effect::PcUpdate { value }) => {
            branch_discr_from_final_pc_update(block, value, target_addr, fallthrough_addr)
        }
        _ => Err(unresolved_control_flow_error(format!(
            "block {} at 0x{:x} has two CFG successors but no conditional branch semantics",
            block.id, block.start_addr
        ))),
    }
}

fn strict_cfg_edges(block: &LiftedBlock, cfg: &Cfg) -> Result<Vec<CfgEdge>, LiftError> {
    let edges = cfg.edges_for_block(block);
    if let Some(edge) = edges.iter().find(|edge| {
        edge.kind.is_strict_control_flow() && matches!(edge.target, CfgEdgeTarget::Unresolved)
    }) {
        return Err(unresolved_control_flow_error(format!(
            "block {} at 0x{:x} has unresolved {:?} target",
            block.id, block.start_addr, edge.kind
        )));
    }
    if let Some(edge) = edges.iter().find(|edge| {
        edge.kind.is_strict_control_flow() && matches!(edge.target, CfgEdgeTarget::External(_))
    }) {
        return Err(unresolved_control_flow_error(format!(
            "block {} at 0x{:x} has external {:?} target without a boundary summary",
            block.id, block.start_addr, edge.kind
        )));
    }
    Ok(edges)
}

fn conditional_edges(edges: &[CfgEdge]) -> Option<(CfgEdge, CfgEdge)> {
    let false_edge = edges.iter().find(|edge| edge.kind == CfgEdgeKind::ConditionalFalse)?;
    let true_edge = edges.iter().find(|edge| edge.kind == CfgEdgeKind::ConditionalTrue)?;
    Some((*false_edge, *true_edge))
}

fn edge_addr(block: &LiftedBlock, edge: CfgEdge) -> Result<u64, LiftError> {
    edge.target.address().ok_or_else(|| {
        unresolved_control_flow_error(format!(
            "block {} at 0x{:x} {:?} edge has no concrete target",
            block.id, block.start_addr, edge.kind
        ))
    })
}

fn edge_block_id(cfg: &Cfg, block: &LiftedBlock, edge: CfgEdge) -> Result<BlockId, LiftError> {
    let Some(addr) = edge.internal_successor() else {
        return Err(missing_successor_error(format!(
            "block {} at 0x{:x} {:?} edge does not target a recovered block",
            block.id, block.start_addr, edge.kind
        )));
    };
    successor_block_id(cfg, block, addr, 0)
}

fn is_external_branch_edge(edge: &CfgEdge) -> bool {
    matches!(
        (edge.kind, edge.target),
        (
            CfgEdgeKind::DirectBranch
                | CfgEdgeKind::ConditionalTrue
                | CfgEdgeKind::ConditionalFalse,
            CfgEdgeTarget::External(_),
        )
    )
}

fn mixed_conditional_external_terminator(
    block: &LiftedBlock,
    cfg: &Cfg,
    effects_for_block: &[Effect],
    state: &MachineState,
    edges: &[CfgEdge],
) -> Result<Terminator, LiftError> {
    let Some((false_edge, true_edge)) = conditional_edges(edges) else {
        return Err(unrepresentable_cfg_error(format!(
            "block {} at 0x{:x} has one CFG successor for a conditional branch but no conditional edge metadata",
            block.id, block.start_addr
        )));
    };

    let false_addr = edge_addr(block, false_edge)?;
    let true_addr = edge_addr(block, true_edge)?;
    let discr = conditional_branch_discr(block, effects_for_block, state, true_addr, false_addr)?;

    let (target_edge, external_addr, expected) = match (false_edge.target, true_edge.target) {
        (CfgEdgeTarget::Internal(_), CfgEdgeTarget::External(addr)) => (false_edge, addr, false),
        (CfgEdgeTarget::External(addr), CfgEdgeTarget::Internal(_)) => (true_edge, addr, true),
        (CfgEdgeTarget::Internal(_), CfgEdgeTarget::Internal(_)) => {
            return Err(missing_successor_error(format!(
                "block {} at 0x{:x} has one CFG successor but both conditional arms target recovered blocks",
                block.id, block.start_addr
            )));
        }
        _ => {
            return Err(unrepresentable_cfg_error(format!(
                "block {} at 0x{:x} has one CFG successor for a conditional branch but its other arm is not a concrete external target",
                block.id, block.start_addr
            )));
        }
    };

    let target = edge_block_id(cfg, block, target_edge)?;
    let last_addr = block.instructions.last().map(|i| i.address).unwrap_or(block.start_addr);

    Ok(Terminator::Assert {
        cond: discr,
        expected,
        msg: AssertMessage::Custom(format!("external branch arm to 0x{external_addr:x}")),
        target,
        // Binary lifting has no source-level unwind edge; nounwind (matches the
        // prior no-unwind-field behavior).
        unwind: trust_types::UnwindEdge::Unreachable,
        span: SourceSpan {
            file: format!("binary:0x{last_addr:x}"),
            line_start: 0,
            col_start: 0,
            line_end: 0,
            col_end: 0,
        },
    })
}

/// Determine the TrustIr terminator for a lifted block based on its effects and successors.
///
/// # Trust: #564 — wire condition formulas into SwitchInt
fn block_terminator(
    block: &LiftedBlock,
    cfg: &Cfg,
    effects_for_block: &[Effect],
    state: &MachineState,
) -> Result<Terminator, LiftError> {
    let edges = strict_cfg_edges(block, cfg)?;

    if block.is_return {
        return Ok(Terminator::Return);
    }

    if matches!(block.instructions.last().map(|insn| insn.flow), Some(ControlFlow::Exception)) {
        return Ok(Terminator::Unreachable);
    }

    match block.successors.len() {
        0 if matches!(block.instructions.last().map(|insn| insn.flow), Some(ControlFlow::Call)) => {
            Ok(Terminator::Unreachable)
        }
        0 if edges.iter().any(is_external_branch_edge) => Ok(Terminator::Unreachable),
        0 => Err(missing_successor_error(format!(
            "block {} at 0x{:x} has no successors and is not marked as a return",
            block.id, block.start_addr
        ))),
        1 => {
            if matches!(
                block.instructions.last().map(|insn| insn.flow),
                Some(ControlFlow::ConditionalBranch)
            ) {
                return mixed_conditional_external_terminator(
                    block,
                    cfg,
                    effects_for_block,
                    state,
                    &edges,
                );
            }
            let target = successor_block_id(cfg, block, block.successors[0], 0)?;
            Ok(Terminator::Goto(target))
        }
        2 => {
            let fallthrough = successor_block_id(cfg, block, block.successors[0], 0)?;
            let target = successor_block_id(cfg, block, block.successors[1], 1)?;
            let last_addr =
                block.instructions.last().map(|i| i.address).unwrap_or(block.start_addr);

            // Trust: #564 — extract condition from ConditionalBranch effect, or from a
            // final PC update ITE for branch forms whose semantics update PC directly.
            let discr = conditional_branch_discr(
                block,
                effects_for_block,
                state,
                block.successors[1],
                block.successors[0],
            )?;

            Ok(Terminator::SwitchInt {
                discr,
                targets: vec![(1, target)],
                otherwise: fallthrough,
                exhaustive_enum_unreachable: false,
                span: SourceSpan {
                    file: format!("binary:0x{last_addr:x}"),
                    line_start: 0,
                    col_start: 0,
                    line_end: 0,
                    col_end: 0,
                },
            })
        }
        n => Err(unrepresentable_cfg_error(format!(
            "block {} at 0x{:x} has {n} CFG successors; strict semantic lifting only supports 0, 1, or 2",
            block.id, block.start_addr
        ))),
    }
}

/// Lift an entire CFG into TrustIr blocks using real instruction semantics.
///
/// # Trust: #573 — architecture-aware semantic lifting
///
/// Dispatches to the appropriate ISA semantics and register layout based on
/// the target architecture.
#[cfg(test)]
pub(crate) fn lift_cfg_semantic(
    cfg: &Cfg,
    arch: LiftArch,
) -> Result<(Vec<TrustIrBlock>, LocalLayout), LiftError> {
    let (blocks, layout, _) = lift_cfg_semantic_with_facts(cfg, arch)?;
    Ok((blocks, layout))
}

/// Lift an entire CFG into TrustIr and preserve proof-relevant binary memory facts.
#[cfg(test)]
pub(crate) fn lift_cfg_semantic_with_facts(
    cfg: &Cfg,
    arch: LiftArch,
) -> Result<(Vec<TrustIrBlock>, LocalLayout, Vec<MemoryAccessFact>), LiftError> {
    let (blocks, layout, facts, _) =
        lift_cfg_semantic_with_region_hints(cfg, arch, MemoryRegionHints::default())?;
    Ok((blocks, layout, facts))
}

#[cfg(test)]
pub(crate) fn lift_cfg_semantic_with_facts_and_ledger(
    cfg: &Cfg,
    arch: LiftArch,
) -> Result<(Vec<TrustIrBlock>, LocalLayout, Vec<MemoryAccessFact>, UnsupportedLedger), LiftError> {
    lift_cfg_semantic_with_region_hints(cfg, arch, MemoryRegionHints::default())
}

/// Lift an entire CFG into TrustIr using loader-derived memory region hints.
pub(crate) fn lift_cfg_semantic_with_region_hints(
    cfg: &Cfg,
    arch: LiftArch,
    region_hints: MemoryRegionHints,
) -> Result<(Vec<TrustIrBlock>, LocalLayout, Vec<MemoryAccessFact>, UnsupportedLedger), LiftError> {
    match arch {
        LiftArch::Aarch64 => lift_cfg_with_semantics(
            cfg,
            arch,
            &Aarch64Semantics,
            LocalLayout::aarch64(),
            region_hints,
        ),
        LiftArch::X86_64 => lift_cfg_with_semantics(
            cfg,
            arch,
            &X86_64Semantics,
            LocalLayout::x86_64(),
            region_hints,
        ),
    }
}

/// Inner lifting loop, generic over the ISA semantics implementation.
fn lift_cfg_with_semantics(
    cfg: &Cfg,
    arch: LiftArch,
    semantics: &dyn Semantics,
    layout: LocalLayout,
    region_hints: MemoryRegionHints,
) -> Result<(Vec<TrustIrBlock>, LocalLayout, Vec<MemoryAccessFact>, UnsupportedLedger), LiftError> {
    let mut trust_ir_blocks = Vec::with_capacity(cfg.blocks.len());
    let mut memory_accesses = Vec::new();
    let mut unsupported = UnsupportedLedger::default();
    let function_entry = cfg
        .blocks
        .get(cfg.entry)
        .map(|block| block.start_addr)
        .or_else(|| cfg.blocks.first().map(|block| block.start_addr));

    for block in &cfg.blocks {
        let mut stmts = Vec::new();
        let mut state = MachineState::symbolic();
        let mut aarch64_provenance = Aarch64AddressProvenanceState::default();
        let mut block_effects: Vec<Effect> = Vec::new();

        for (insn_index, insn) in block.instructions.iter().enumerate() {
            state.pc = trust_types::Formula::BitVec { value: insn.address as i128, width: 64 };
            let accepted_aarch64_ordering_role = (arch == LiftArch::Aarch64)
                .then(|| aarch64_accepted_release_acquire_slice_role(block, insn_index))
                .flatten();

            if arch == LiftArch::Aarch64
                && accepted_aarch64_ordering_role.is_none()
                && let Some((category, detail)) = unsupported_aarch64_semantics_reason(insn)
            {
                return Err(unsupported_aarch64_instruction_semantics_error(
                    function_entry,
                    insn,
                    category,
                    &detail,
                ));
            }
            if arch == LiftArch::X86_64
                && let Some((category, detail)) = unsupported_x86_64_semantics_reason(insn)
            {
                return Err(unsupported_x86_64_instruction_semantics_error(
                    function_entry,
                    insn,
                    category,
                    &detail,
                ));
            }

            if arch == LiftArch::Aarch64
                && let Some(feature) = modeled_partial_aarch64_semantic_feature(insn)
            {
                unsupported.records.push(unsupported_record_for_instruction(
                    "trust-lift::semantic-lift",
                    feature,
                    function_entry,
                    arch,
                    insn,
                ));
            }
            if arch == LiftArch::X86_64
                && let Some(feature) = modeled_partial_x86_64_semantic_feature(insn)
            {
                unsupported.records.push(unsupported_record_for_instruction(
                    "trust-lift::semantic-lift",
                    feature,
                    function_entry,
                    arch,
                    insn,
                ));
            }

            let effects = aarch64_local_effects(&state, insn).transpose()?.map_or_else(
                || {
                    semantics
                        .effects(&state, insn)
                        .map_err(|err| machine_semantics_error(arch, function_entry, insn, err))
                },
                Ok,
            )?;

            for effect in &effects {
                if arch == LiftArch::Aarch64
                    && accepted_aarch64_ordering_role.is_none()
                    && matches!(effect, Effect::Aarch64SyncBoundary { .. })
                {
                    unsupported.records.push(aarch64_sync_boundary_record(
                        function_entry,
                        arch,
                        insn,
                        effect,
                    ));
                }
                if arch == LiftArch::Aarch64
                    && accepted_aarch64_ordering_role.is_none()
                    && matches!(effect, Effect::Aarch64AtomicAccess { .. })
                {
                    unsupported.records.push(aarch64_atomic_access_record(
                        function_entry,
                        arch,
                        insn,
                        effect,
                    ));
                }

                if let Some(function_entry) = function_entry {
                    let provenance = if arch == LiftArch::Aarch64 {
                        aarch64_memory_access_provenance(&aarch64_provenance, insn)
                    } else {
                        None
                    };
                    if let Some(fact) =
                        memory_access_fact(function_entry, insn, effect, region_hints, provenance)
                    {
                        let mut fact = fact;
                        if let Some(role) = accepted_aarch64_ordering_role {
                            annotate_aarch64_accepted_ordering_access(
                                &mut fact,
                                function_entry,
                                block,
                                role,
                            );
                        }
                        if arch == LiftArch::Aarch64
                            && insn.opcode == Opcode::LdrLiteral
                            && fact.region == MemoryRegionKind::Unknown
                        {
                            unsupported.records.push(unsupported_record_for_instruction(
                                "trust-lift::memory-provenance",
                                "unclassified AArch64 literal load region",
                                Some(function_entry),
                                arch,
                                insn,
                            ));
                        }
                        memory_accesses.push(fact);
                    }
                }
                let mut new_stmts = effect_to_stmts(effect, &layout, insn.address)?;
                stmts.append(&mut new_stmts);
                apply_effect_to_state(&mut state, effect);
                if arch == LiftArch::Aarch64 {
                    aarch64_provenance.apply_effect(insn, effect);
                }
                block_effects.push(effect.clone());
            }
        }

        stmts.retain(|s| !matches!(s, Statement::Nop));
        let terminator = block_terminator(block, cfg, &block_effects, &state)?;

        trust_ir_blocks.push(TrustIrBlock { id: BlockId(block.id), stmts, terminator });
    }

    Ok((trust_ir_blocks, layout, memory_accesses, unsupported))
}

fn aarch64_local_effects(
    state: &MachineState,
    insn: &Instruction,
) -> Option<Result<Vec<Effect>, LiftError>> {
    match insn.opcode {
        Opcode::Add | Opcode::Adds | Opcode::Sub | Opcode::Subs
            if matches!(insn.operand(2), Some(DisasmOperand::ExtendedReg { .. })) =>
        {
            Some(aarch64_add_sub_extended_reg_effects(state, insn))
        }
        Opcode::Ldr
            if matches!(
                insn.operand(1),
                Some(DisasmOperand::Mem(DisasmMemoryOperand::BaseRegister { extend: Some(_), .. }))
            ) =>
        {
            Some(aarch64_ldr_register_offset_effects(state, insn))
        }
        Opcode::BCond => Some(aarch64_bcond_effects(state, insn)),
        Opcode::LdrLiteral => Some(aarch64_ldr_literal_effects(state, insn)),
        Opcode::Prfm | Opcode::Yield | Opcode::Sev | Opcode::Sevl => {
            Some(Ok(vec![pc_advance_by_size(state, insn)]))
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Aarch64AddressProvenance {
    PcRelative,
}

#[derive(Debug, Clone, Default)]
struct Aarch64AddressProvenanceState {
    gpr: [Option<Aarch64AddressProvenance>; 31],
}

impl Aarch64AddressProvenanceState {
    fn get(&self, reg: Register) -> Option<Aarch64AddressProvenance> {
        (reg.kind == RegKind::Gpr)
            .then_some(usize::from(reg.index))
            .filter(|index| *index < self.gpr.len())
            .and_then(|index| self.gpr[index])
    }

    fn apply_effect(&mut self, insn: &Instruction, effect: &Effect) {
        if let Effect::RegWrite { index, width, .. } = effect {
            let index = usize::from(*index);
            if index < self.gpr.len() {
                self.gpr[index] = aarch64_reg_write_address_provenance(self, insn, index, *width);
            }
        }
    }
}

fn aarch64_reg_write_address_provenance(
    state: &Aarch64AddressProvenanceState,
    insn: &Instruction,
    written_index: usize,
    written_width: u32,
) -> Option<Aarch64AddressProvenance> {
    if written_width != 64 {
        return None;
    }

    let dst = aarch64_gpr_operand(insn, 0)?;
    if usize::from(dst.index) != written_index {
        return None;
    }

    match insn.opcode {
        Opcode::Adr | Opcode::Adrp => Some(Aarch64AddressProvenance::PcRelative),
        Opcode::Add | Opcode::Sub if aarch64_static_offset_operand(insn.operand(2)) => {
            state.get(aarch64_gpr_operand(insn, 1)?)
        }
        _ => None,
    }
}

fn aarch64_memory_access_provenance(
    state: &Aarch64AddressProvenanceState,
    insn: &Instruction,
) -> Option<Aarch64AddressProvenance> {
    let mem = insn.operands().find_map(|operand| {
        if let DisasmOperand::Mem(mem) = operand { Some(*mem) } else { None }
    })?;

    match mem {
        DisasmMemoryOperand::Base { base }
        | DisasmMemoryOperand::BaseOffset { base, .. }
        | DisasmMemoryOperand::PreIndex { base, .. }
        | DisasmMemoryOperand::PostIndex { base, .. } => state.get(base),
        DisasmMemoryOperand::BaseRegister { .. } | DisasmMemoryOperand::PcRelative { .. } => None,
        _ => None,
    }
}

fn aarch64_gpr_operand(insn: &Instruction, operand_index: usize) -> Option<Register> {
    match insn.operand(operand_index) {
        Some(DisasmOperand::Reg(reg)) if reg.kind == RegKind::Gpr => Some(*reg),
        _ => None,
    }
}

fn aarch64_static_offset_operand(operand: Option<&DisasmOperand>) -> bool {
    matches!(operand, Some(DisasmOperand::Imm(_)) | Some(DisasmOperand::SignedImm(_)))
}

fn aarch64_add_sub_extended_reg_effects(
    state: &MachineState,
    insn: &Instruction,
) -> Result<Vec<Effect>, LiftError> {
    let dst = match insn.operand(0) {
        Some(DisasmOperand::Reg(dst)) => *dst,
        _ => {
            return Err(aarch64_operand_error(
                insn,
                0,
                "expected destination register for add/sub extended-register form",
            ));
        }
    };
    let lhs_reg = match insn.operand(1) {
        Some(DisasmOperand::Reg(lhs)) => *lhs,
        _ => {
            return Err(aarch64_operand_error(
                insn,
                1,
                "expected left operand register for add/sub extended-register form",
            ));
        }
    };
    let (index_reg, extend, shift) = match insn.operand(2) {
        Some(DisasmOperand::ExtendedReg { reg, extend, shift }) => (*reg, *extend, *shift),
        _ => {
            return Err(aarch64_operand_error(
                insn,
                2,
                "expected extended register operand for add/sub extended-register form",
            ));
        }
    };

    let width = u32::from(dst.width);
    if !matches!(width, 32 | 64) {
        return Err(aarch64_operand_error(
            insn,
            0,
            format!("destination width {width} is outside the scalar GPR subset"),
        ));
    }

    let lhs = aarch64_register_formula(state, lhs_reg, width, insn, 1)?;
    let rhs = aarch64_extended_register_formula(state, index_reg, extend, shift, width, insn, 2)?;
    let is_sub = matches!(insn.opcode, Opcode::Sub | Opcode::Subs);
    let sets_flags = matches!(insn.opcode, Opcode::Adds | Opcode::Subs);
    let result = if is_sub {
        Formula::BvSub(Box::new(lhs.clone()), Box::new(rhs.clone()), width)
    } else {
        Formula::BvAdd(Box::new(lhs.clone()), Box::new(rhs.clone()), width)
    };

    let mut effects = Vec::new();
    if !dst.is_zero_register() {
        effects.push(aarch64_write_register_effect(dst, width, result.clone(), insn)?);
    }
    if sets_flags {
        effects.push(aarch64_add_sub_flag_update(&lhs, &rhs, &result, width, is_sub));
    }
    effects.push(pc_advance_by_size(state, insn));
    Ok(effects)
}

fn aarch64_ldr_register_offset_effects(
    state: &MachineState,
    insn: &Instruction,
) -> Result<Vec<Effect>, LiftError> {
    let dst = match insn.operand(0) {
        Some(DisasmOperand::Reg(dst)) => *dst,
        _ => {
            return Err(aarch64_operand_error(
                insn,
                0,
                "expected scalar destination register for register-offset load",
            ));
        }
    };
    let (base, index, extend, shift) = match insn.operand(1) {
        Some(DisasmOperand::Mem(DisasmMemoryOperand::BaseRegister {
            base,
            index,
            extend: Some(extend),
            shift,
        })) => (*base, *index, *extend, *shift),
        _ => {
            return Err(aarch64_operand_error(
                insn,
                1,
                "expected extended register-offset memory operand",
            ));
        }
    };

    let width = u32::from(dst.width);
    if !matches!(width, 32 | 64) {
        return Err(aarch64_operand_error(
            insn,
            0,
            format!("load destination width {width} is outside the scalar GPR subset"),
        ));
    }

    let address = aarch64_register_offset_address(state, base, index, extend, shift, insn)?;
    let width_bytes = width / 8;
    let loaded = byte_load_formula(&state.memory, &address, width_bytes, width);

    Ok(vec![
        Effect::MemRead { address: address.clone(), width_bytes },
        Effect::RegWrite { index: dst.index, width, value: loaded },
        pc_advance_by_size(state, insn),
    ])
}

fn aarch64_register_offset_address(
    state: &MachineState,
    base: Register,
    index: Register,
    extend: ExtendType,
    shift: u8,
    insn: &Instruction,
) -> Result<Formula, LiftError> {
    let base_value = aarch64_register_formula(state, base, 64, insn, 1)?;
    let index_value = aarch64_extended_register_formula(state, index, extend, shift, 64, insn, 1)?;
    Ok(Formula::BvAdd(Box::new(base_value), Box::new(index_value), 64))
}

fn aarch64_register_formula(
    state: &MachineState,
    reg: Register,
    width: u32,
    insn: &Instruction,
    operand_index: usize,
) -> Result<Formula, LiftError> {
    match reg.kind {
        RegKind::Gpr => Ok(state.read_gpr(reg.index, width)),
        RegKind::Sp => Ok(state.read_sp(width)),
        RegKind::Zr => Ok(Formula::BitVec { value: 0, width }),
        _ => Err(aarch64_operand_error(
            insn,
            operand_index,
            format!("unsupported register class {:?} for scalar AArch64 lift", reg.kind),
        )),
    }
}

fn aarch64_write_register_effect(
    dst: Register,
    width: u32,
    value: Formula,
    insn: &Instruction,
) -> Result<Effect, LiftError> {
    match dst.kind {
        RegKind::Gpr | RegKind::Zr => Ok(Effect::RegWrite { index: dst.index, width, value }),
        RegKind::Sp => {
            let value =
                if width < 64 { Formula::BvZeroExt(Box::new(value), 64 - width) } else { value };
            Ok(Effect::SpWrite { value })
        }
        _ => Err(aarch64_operand_error(
            insn,
            0,
            format!("unsupported destination register class {:?}", dst.kind),
        )),
    }
}

fn aarch64_extended_register_formula(
    state: &MachineState,
    reg: Register,
    extend: ExtendType,
    shift: u8,
    width: u32,
    insn: &Instruction,
    operand_index: usize,
) -> Result<Formula, LiftError> {
    if shift > 4 {
        return Err(aarch64_operand_error(
            insn,
            operand_index,
            format!("extended-register shift #{shift} exceeds the AArch64 scalar limit"),
        ));
    }

    let source_width = aarch64_extend_source_width(extend).ok_or_else(|| {
        aarch64_operand_error(
            insn,
            operand_index,
            format!("unsupported AArch64 extend type {extend:?}"),
        )
    })?;
    if source_width > width {
        return Err(aarch64_operand_error(
            insn,
            operand_index,
            format!("extend source width {source_width} exceeds destination width {width}"),
        ));
    }

    let raw = aarch64_register_formula(state, reg, source_width, insn, operand_index)?;
    let extended = if source_width == width {
        raw
    } else if aarch64_extend_is_signed(extend) {
        Formula::BvSignExt(Box::new(raw), width - source_width)
    } else {
        Formula::BvZeroExt(Box::new(raw), width - source_width)
    };

    if shift == 0 {
        Ok(extended)
    } else {
        Ok(Formula::BvShl(
            Box::new(extended),
            Box::new(Formula::BitVec { value: i128::from(shift), width }),
            width,
        ))
    }
}

fn aarch64_extend_source_width(extend: ExtendType) -> Option<u32> {
    match extend {
        ExtendType::Uxtb | ExtendType::Sxtb => Some(8),
        ExtendType::Uxth | ExtendType::Sxth => Some(16),
        ExtendType::Uxtw | ExtendType::Sxtw => Some(32),
        ExtendType::Uxtx | ExtendType::Sxtx => Some(64),
        _ => None,
    }
}

fn aarch64_extend_is_signed(extend: ExtendType) -> bool {
    matches!(extend, ExtendType::Sxtb | ExtendType::Sxth | ExtendType::Sxtw | ExtendType::Sxtx)
}

fn aarch64_add_sub_flag_update(
    lhs: &Formula,
    rhs: &Formula,
    result: &Formula,
    width: u32,
    is_sub: bool,
) -> Effect {
    let sign_bit = width - 1;
    let n = Formula::Eq(
        Box::new(Formula::BvExtract {
            inner: Box::new(result.clone()),
            high: sign_bit,
            low: sign_bit,
        }),
        Box::new(Formula::BitVec { value: 1, width: 1 }),
    );
    let z = Formula::Eq(Box::new(result.clone()), Box::new(Formula::BitVec { value: 0, width }));
    let c = if is_sub {
        Formula::Not(Box::new(Formula::BvULt(Box::new(lhs.clone()), Box::new(rhs.clone()), width)))
    } else {
        Formula::BvULt(Box::new(result.clone()), Box::new(lhs.clone()), width)
    };

    let lhs_sign =
        Formula::BvExtract { inner: Box::new(lhs.clone()), high: sign_bit, low: sign_bit };
    let rhs_sign =
        Formula::BvExtract { inner: Box::new(rhs.clone()), high: sign_bit, low: sign_bit };
    let result_sign =
        Formula::BvExtract { inner: Box::new(result.clone()), high: sign_bit, low: sign_bit };
    let signs_match = Formula::Eq(Box::new(lhs_sign.clone()), Box::new(rhs_sign));
    let result_differs =
        Formula::Not(Box::new(Formula::Eq(Box::new(result_sign), Box::new(lhs_sign))));
    let v = if is_sub {
        Formula::And(vec![Formula::Not(Box::new(signs_match)), result_differs])
    } else {
        Formula::And(vec![signs_match, result_differs])
    };

    Effect::FlagUpdate { n, z, c, v }
}

fn aarch64_operand_error(
    insn: &Instruction,
    operand_index: usize,
    detail: impl Into<String>,
) -> LiftError {
    unsupported_semantics_error(format!(
        "unsupported instruction semantics at binary:0x{:x} {} opcode {:?}: operand {operand_index}: {}",
        insn.address,
        instruction_provenance_detail(insn),
        insn.opcode,
        detail.into()
    ))
}

fn aarch64_bcond_effects(
    state: &MachineState,
    insn: &Instruction,
) -> Result<Vec<Effect>, LiftError> {
    let target = match insn
        .operands()
        .find_map(|op| if let DisasmOperand::PcRelAddr(addr) = op { Some(*addr) } else { None })
    {
        Some(addr) => Formula::BitVec { value: addr as i128, width: 64 },
        None => {
            return Err(unsupported_semantics_error(format!(
                "unsupported instruction semantics at binary:0x{:x} {} opcode {:?}: expected PC-relative target for conditional branch",
                insn.address,
                instruction_provenance_detail(insn),
                insn.opcode
            )));
        }
    };
    let condition = aarch64_condition_operand(insn)?;
    let fallthrough = next_pc_formula(state, insn);
    let pc_value = Formula::Ite(
        Box::new(trust_machine_sem::condition_to_formula(state, condition)),
        Box::new(target.clone()),
        Box::new(fallthrough.clone()),
    );

    Ok(vec![
        Effect::ConditionalBranch { condition, target, fallthrough },
        Effect::PcUpdate { value: pc_value },
    ])
}

fn aarch64_condition_operand(insn: &Instruction) -> Result<Condition, LiftError> {
    insn.operands()
        .find_map(|op| {
            if let DisasmOperand::Cond(cond) = op { Some(*cond) } else { None }
        })
        .ok_or_else(|| {
            unsupported_semantics_error(format!(
                "unsupported instruction semantics at binary:0x{:x} {} opcode {:?}: expected condition code for conditional branch",
                insn.address,
                instruction_provenance_detail(insn),
                insn.opcode
            ))
        })
}

fn aarch64_ldr_literal_effects(
    state: &MachineState,
    insn: &Instruction,
) -> Result<Vec<Effect>, LiftError> {
    let dst = match insn.operand(0) {
        Some(DisasmOperand::Reg(dst)) => *dst,
        _ => {
            return Err(unsupported_aarch64_instruction_semantics_error(
                None,
                insn,
                "AArch64 literal load",
                &aarch64_literal_load_blocker_detail(
                    "expected scalar destination register for literal load",
                ),
            ));
        }
    };
    if !matches!(dst.kind, RegKind::Gpr | RegKind::Zr) {
        return Err(unsupported_aarch64_instruction_semantics_error(
            None,
            insn,
            "AArch64 literal load",
            &aarch64_literal_load_blocker_detail(format!(
                "literal load destination {dst} uses unsupported register class {:?}",
                dst.kind
            )),
        ));
    }
    let offset = match insn.operand(1) {
        Some(DisasmOperand::Mem(DisasmMemoryOperand::PcRelative { offset })) => offset,
        _ => {
            return Err(unsupported_aarch64_instruction_semantics_error(
                None,
                insn,
                "AArch64 literal load",
                &aarch64_literal_load_blocker_detail("expected PC-relative literal operand"),
            ));
        }
    };
    let width = u32::from(dst.width);
    if !matches!(width, 32 | 64) {
        return Err(unsupported_aarch64_instruction_semantics_error(
            None,
            insn,
            "AArch64 literal load",
            &aarch64_literal_load_blocker_detail(format!(
                "literal load width {width} is outside the scalar GPR subset"
            )),
        ));
    }

    let address = Formula::BvAdd(
        Box::new(Formula::Var("PC".into(), trust_types::Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: i128::from(*offset), width: 64 }),
        64,
    );
    let width_bytes = width / 8;
    let loaded = byte_load_formula(&state.memory, &address, width_bytes, width);
    Ok(vec![
        Effect::MemRead { address, width_bytes },
        Effect::RegWrite { index: dst.index, width, value: loaded },
        pc_advance_by_size(state, insn),
    ])
}

fn pc_advance_by_size(state: &MachineState, insn: &Instruction) -> Effect {
    Effect::PcUpdate { value: next_pc_formula(state, insn) }
}

fn next_pc_formula(state: &MachineState, insn: &Instruction) -> Formula {
    Formula::BvAdd(
        Box::new(state.pc.clone()),
        Box::new(Formula::BitVec { value: i128::from(insn.size), width: 64 }),
        64,
    )
}

fn unsupported_record_for_instruction(
    stage: impl Into<String>,
    feature: impl Into<String>,
    function_entry: Option<u64>,
    arch: LiftArch,
    insn: &Instruction,
) -> UnsupportedRecord {
    UnsupportedRecord {
        stage: stage.into(),
        architecture: Some(arch_name(arch).into()),
        origin: Some(binary_origin_for_instruction(function_entry.unwrap_or(insn.address), insn)),
        opcode: Some(format!("{:?}", insn.opcode)),
        operand: unsupported_operand_detail(arch, insn),
        feature: feature.into(),
    }
}

fn unsupported_aarch64_semantics_record(
    function_entry: Option<u64>,
    arch: LiftArch,
    insn: &Instruction,
    category: &str,
    detail: &str,
) -> UnsupportedRecord {
    unsupported_record_for_instruction(
        "trust-lift::semantic-lift",
        format!("{category} semantics are unsupported fail-closed: {detail}"),
        function_entry,
        arch,
        insn,
    )
}

fn aarch64_sync_boundary_record(
    function_entry: Option<u64>,
    arch: LiftArch,
    insn: &Instruction,
    effect: &Effect,
) -> UnsupportedRecord {
    let Effect::Aarch64SyncBoundary { kind, scope, ordering, clears_exclusive_monitor, raw_option } =
        effect
    else {
        unreachable!("aarch64_sync_boundary_record requires a sync boundary effect")
    };

    let feature = format!(
        "AArch64 synchronization boundary modeled as explicit partial unsupported-ledger boundary; kind={kind:?}; scope={scope:?}; ordering={ordering:?}; clears_exclusive_monitor={clears_exclusive_monitor}; raw_option={}; not proof-grade until ordering/monitor witnesses are proof-consumed",
        raw_option.map_or_else(|| "none".to_string(), |option| format!("0x{option:x}"))
    );

    unsupported_record_for_instruction(
        "trust-lift::semantic-lift",
        feature,
        function_entry,
        arch,
        insn,
    )
}

fn aarch64_atomic_access_record(
    function_entry: Option<u64>,
    arch: LiftArch,
    insn: &Instruction,
    effect: &Effect,
) -> UnsupportedRecord {
    let Effect::Aarch64AtomicAccess { kind, ordering, width_bytes, exclusive, .. } = effect else {
        unreachable!("aarch64_atomic_access_record requires an atomic access effect")
    };

    let feature = format!(
        "AArch64 atomic memory-order access modeled as explicit partial unsupported-ledger boundary; typed proof-blocker: kind={kind:?}; ordering={ordering:?}; ordering_scope=per-access; width_bytes={width_bytes}; exclusive={exclusive}; scalar data-plane remains represented by separate MemRead/RegWrite or MemWrite effects; status=not proof-consumed; not proof-grade until ordering event, synchronization edge, thread identity, and happens-before witnesses are proof-consumed"
    );

    unsupported_record_for_instruction(
        "trust-lift::semantic-lift",
        feature,
        function_entry,
        arch,
        insn,
    )
}

fn unsupported_operand_detail(arch: LiftArch, insn: &Instruction) -> Option<String> {
    match arch {
        LiftArch::Aarch64 => aarch64_unsupported_operand_detail(insn),
        LiftArch::X86_64 => x86_64_unsupported_operand_detail(insn),
    }
}

fn aarch64_unsupported_operand_detail(insn: &Instruction) -> Option<String> {
    aarch64_barrier_operand_detail(insn)
        .or_else(|| aarch64_atomic_operand_detail(insn))
        .or_else(|| aarch64_fp_simd_operand_detail(insn))
}

fn x86_64_unsupported_operand_detail(insn: &Instruction) -> Option<String> {
    let operands = disasm_operand_list_display(insn);
    (operands != "unavailable").then_some(operands)
}

fn aarch64_atomic_operand_detail(insn: &Instruction) -> Option<String> {
    if !matches!(
        insn.opcode,
        Opcode::Ldar | Opcode::Stlr | Opcode::Ldxr | Opcode::Stxr | Opcode::Ldaxr | Opcode::Stlxr
    ) {
        return None;
    }

    let operands = (0..insn.operand_count())
        .filter_map(|index| insn.operand(index).map(|operand| format!("{operand:?}")))
        .collect::<Vec<_>>()
        .join(", ");

    if operands.is_empty() { None } else { Some(operands) }
}

fn aarch64_fp_simd_operand_detail(insn: &Instruction) -> Option<String> {
    let has_simd_operand = insn
        .operands()
        .any(|operand| matches!(operand, DisasmOperand::Reg(reg) if reg.kind == RegKind::Simd));
    if !has_simd_operand {
        return None;
    }

    let operands = (0..insn.operand_count())
        .filter_map(|index| insn.operand(index).map(|operand| format!("{operand:?}")))
        .collect::<Vec<_>>()
        .join(", ");

    if operands.is_empty() { None } else { Some(operands) }
}

fn arch_name(arch: LiftArch) -> &'static str {
    match arch {
        LiftArch::Aarch64 => "aarch64",
        LiftArch::X86_64 => "x86_64",
    }
}

fn memory_access_fact(
    function_entry: u64,
    insn: &Instruction,
    effect: &Effect,
    region_hints: MemoryRegionHints,
    address_provenance: Option<Aarch64AddressProvenance>,
) -> Option<MemoryAccessFact> {
    let (kind, address, width_bytes) = match effect {
        Effect::MemRead { address, width_bytes } => {
            (MemoryAccessKind::Read, address.clone(), *width_bytes)
        }
        Effect::MemWrite { address, width_bytes, .. } => {
            (MemoryAccessKind::Write, address.clone(), *width_bytes)
        }
        _ => return None,
    };

    let metadata = classify_memory_access(&address, insn, region_hints, address_provenance);

    Some(MemoryAccessFact {
        origin: binary_origin_for_instruction(function_entry, insn),
        kind,
        address,
        width_bytes,
        endianness: Endianness::Little,
        region: metadata.region,
        base_object: metadata.base_object,
        offset: metadata.offset,
        extent: metadata.extent,
        provenance: metadata.provenance,
        taint: vec![],
    })
}

fn binary_origin_for_instruction(function_entry: u64, insn: &Instruction) -> BinaryOrigin {
    BinaryOrigin {
        binary_path: None,
        function_entry: Some(function_entry),
        instruction_address: insn.address,
        instruction_size: Some(insn.size),
        encoding: Some(insn.encoding),
        instruction_bytes: insn.bytes.clone(),
        source: None,
    }
}

#[derive(Debug, Default)]
struct MemoryRegionMetadata {
    region: MemoryRegionKind,
    base_object: Option<String>,
    offset: Option<Formula>,
    extent: Option<u64>,
    provenance: Option<String>,
}

fn classify_memory_access(
    address: &Formula,
    insn: &Instruction,
    region_hints: MemoryRegionHints,
    address_provenance: Option<Aarch64AddressProvenance>,
) -> MemoryRegionMetadata {
    if let Some(offset) = stack_relative_offset(address) {
        return MemoryRegionMetadata {
            region: MemoryRegionKind::Stack,
            base_object: Some("SP".into()),
            offset: Some(Formula::BitVec { value: offset, width: 64 }),
            extent: None,
            provenance: Some("stack-relative address rooted at SP".into()),
        };
    }

    if let Some(resolved) = concrete_address(address, insn.address) {
        if let Some((text_base, text_size)) = region_hints.contains_text_addr(resolved.address) {
            return MemoryRegionMetadata {
                region: MemoryRegionKind::Global,
                base_object: Some(".text".into()),
                offset: Some(Formula::BitVec {
                    value: i128::from(resolved.address - text_base),
                    width: 64,
                }),
                extent: Some(text_size),
                provenance: Some("loader text-section address".into()),
            };
        }

        if resolved.pc_relative || address_provenance == Some(Aarch64AddressProvenance::PcRelative)
        {
            return MemoryRegionMetadata {
                region: MemoryRegionKind::Global,
                base_object: Some("pc-relative".into()),
                offset: Some(Formula::BitVec { value: i128::from(resolved.address), width: 64 }),
                extent: None,
                provenance: Some("PC-relative memory address".into()),
            };
        }
    }

    MemoryRegionMetadata::default()
}

fn stack_relative_offset(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Var(name, _) if name == "SP" => Some(0),
        Formula::SymVar(sym, _) if sym.as_str() == "SP" => Some(0),
        Formula::BvAdd(lhs, rhs, 64) => {
            if let (Some(offset), Some(constant)) =
                (stack_relative_offset(lhs), bitvec_const_i128(rhs))
            {
                return Some(offset + constant);
            }
            if let (Some(constant), Some(offset)) =
                (bitvec_const_i128(lhs), stack_relative_offset(rhs))
            {
                return Some(constant + offset);
            }
            None
        }
        Formula::BvSub(lhs, rhs, 64) => {
            let offset = stack_relative_offset(lhs)?;
            let constant = bitvec_const_i128(rhs)?;
            Some(offset - constant)
        }
        _ => None,
    }
}

fn bitvec_const_i128(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::BitVec { value, width: 64 } => Some(*value),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
struct ConcreteAddress {
    address: u64,
    pc_relative: bool,
}

impl ConcreteAddress {
    fn add(self, rhs: Self) -> Self {
        Self {
            address: self.address.wrapping_add(rhs.address),
            pc_relative: self.pc_relative || rhs.pc_relative,
        }
    }

    fn sub(self, rhs: Self) -> Self {
        Self {
            address: self.address.wrapping_sub(rhs.address),
            pc_relative: self.pc_relative || rhs.pc_relative,
        }
    }
}

fn concrete_address(formula: &Formula, pc: u64) -> Option<ConcreteAddress> {
    match formula {
        Formula::BitVec { value, width: 64 } => {
            Some(ConcreteAddress { address: i128_to_wrapping_u64(*value), pc_relative: false })
        }
        Formula::Var(name, _) if name == "PC" => {
            Some(ConcreteAddress { address: pc, pc_relative: true })
        }
        Formula::SymVar(sym, _) if sym.as_str() == "PC" => {
            Some(ConcreteAddress { address: pc, pc_relative: true })
        }
        Formula::BvAdd(lhs, rhs, 64) => {
            Some(concrete_address(lhs, pc)?.add(concrete_address(rhs, pc)?))
        }
        Formula::BvSub(lhs, rhs, 64) => {
            Some(concrete_address(lhs, pc)?.sub(concrete_address(rhs, pc)?))
        }
        _ => None,
    }
}

fn i128_to_wrapping_u64(value: i128) -> u64 {
    let modulus = 1_i128 << 64;
    value.rem_euclid(modulus) as u64
}

/// Update the symbolic MachineState based on an Effect.
fn apply_effect_to_state(state: &mut MachineState, effect: &Effect) {
    match effect {
        Effect::RegWrite { index, value, .. } if (*index as usize) < state.gpr.len() => {
            state.gpr[*index as usize] = value.clone();
        }
        Effect::SpWrite { value } => {
            state.sp = value.clone();
        }
        Effect::PcUpdate { value } => {
            state.pc = value.clone();
        }
        Effect::MemWrite { address, value, width_bytes } => {
            state.memory = byte_store_formula(state.memory.clone(), address, value, *width_bytes);
        }
        Effect::FlagUpdate { n, z, c, v } => {
            state.flags.n = n.clone();
            state.flags.z = z.clone();
            state.flags.c = c.clone();
            state.flags.v = v.clone();
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_aarch64_exclusive_blocker_detail(
        text: &str,
        access: &str,
        ordering: &str,
        monitor_operation: &str,
        reports_status: bool,
    ) {
        assert!(text.contains(&format!("access={access}")), "{text}");
        assert!(text.contains(&format!("ordering={ordering}")), "{text}");
        assert!(text.contains(&format!("monitor_operation={monitor_operation}")), "{text}");
        assert!(text.contains(&format!("reports_status={reports_status}")), "{text}");
        assert!(text.contains("monitor reservation state"), "{text}");
        assert!(text.contains("monitor invalidation"), "{text}");
        assert!(text.contains("thread identity"), "{text}");
        assert!(text.contains("proof-consumed witnesses are required"), "{text}");
        if reports_status {
            assert!(text.contains("store-conditional status result"), "{text}");
        }
    }

    #[test]
    fn test_local_layout_standard() {
        let layout = LocalLayout::standard();
        assert_eq!(layout.gpr(0), 1);
        assert_eq!(layout.gpr(30), 31);
        assert_eq!(layout.sp_local, 32);
        assert_eq!(layout.pc_local, 33);
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_local_layout_aarch64() {
        let layout = LocalLayout::aarch64();
        assert_eq!(layout.gpr_count, 31);
        assert_eq!(layout.gpr(0), 1);
        assert_eq!(layout.gpr(30), 31);
        assert_eq!(layout.sp_local, 32);
        assert_eq!(layout.pc_local, 33);
        assert_eq!(layout.flag_n, 34);
        assert_eq!(layout.flag_z, 35);
        assert_eq!(layout.flag_c, 36);
        assert_eq!(layout.flag_v, 37);
        assert_eq!(layout.mem_local, 38);
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_local_layout_x86_64() {
        let layout = LocalLayout::x86_64();
        assert_eq!(layout.gpr_count, 16);
        assert_eq!(layout.gpr(0), 1); // RAX
        assert_eq!(layout.gpr(15), 16); // R15
        assert_eq!(layout.sp_local, 17);
        assert_eq!(layout.pc_local, 18);
        assert_eq!(layout.flag_n, 19); // CF
        assert_eq!(layout.flag_z, 20); // ZF
        assert_eq!(layout.flag_c, 21); // SF
        assert_eq!(layout.flag_v, 22); // OF
        assert_eq!(layout.mem_local, 23);
        assert_eq!(layout.total, 24);
    }

    #[test]
    fn test_local_decls_count() {
        let layout = LocalLayout::standard();
        let decls = layout.to_local_decls();
        assert_eq!(decls.len(), layout.total);
    }

    #[test]
    fn test_local_decls_count_x86_64() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        assert_eq!(decls.len(), layout.total);
    }

    #[test]
    fn test_x86_64_gpr_names() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        assert_eq!(decls[1].name.as_deref(), Some("RAX"));
        assert_eq!(decls[2].name.as_deref(), Some("RCX"));
        assert_eq!(decls[3].name.as_deref(), Some("RDX"));
        assert_eq!(decls[4].name.as_deref(), Some("RBX"));
        assert_eq!(decls[5].name.as_deref(), Some("RSP"));
        assert_eq!(decls[6].name.as_deref(), Some("RBP"));
        assert_eq!(decls[7].name.as_deref(), Some("RSI"));
        assert_eq!(decls[8].name.as_deref(), Some("RDI"));
        assert_eq!(decls[9].name.as_deref(), Some("R8"));
        assert_eq!(decls[16].name.as_deref(), Some("R15"));
    }

    #[test]
    fn test_x86_64_flag_names() {
        let layout = LocalLayout::x86_64();
        let decls = layout.to_local_decls();
        let flag_decls: Vec<_> = decls.iter().filter(|d| d.ty == Ty::Bool).collect();
        assert_eq!(flag_decls.len(), 4);
        assert_eq!(flag_decls[0].name.as_deref(), Some("CF"));
        assert_eq!(flag_decls[1].name.as_deref(), Some("ZF"));
        assert_eq!(flag_decls[2].name.as_deref(), Some("SF"));
        assert_eq!(flag_decls[3].name.as_deref(), Some("OF"));
    }

    #[test]
    fn test_lift_empty_cfg_aarch64() {
        let cfg = Cfg::new();
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("empty CFG should lift");
        assert!(blocks.is_empty());
        assert_eq!(layout.total, 39);
    }

    #[test]
    fn test_lift_empty_cfg_x86_64() {
        let cfg = Cfg::new();
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("empty CFG should lift");
        assert!(blocks.is_empty());
        assert_eq!(layout.total, 24);
    }

    #[test]
    fn test_block_terminator_return() {
        let cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        };
        let state = MachineState::symbolic();
        assert!(matches!(
            block_terminator(&block, &cfg, &[], &state).expect("return terminator"),
            Terminator::Return
        ));
    }

    #[test]
    fn test_block_terminator_missing_successor_fails_strict() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x2000],
            is_return: false,
        };
        cfg.add_block(block.clone());
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state).expect_err("missing successor");
        assert!(matches!(
            &err,
            LiftError::MissingSuccessor {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("successor #0")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: block 0 at 0x1000 successor #0 points to 0x2000, which is not a recovered block"
        );
    }

    #[test]
    fn test_block_terminator_two_successors_requires_condition() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010, 0x1020],
            is_return: false,
        };
        cfg.add_block(block.clone());
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state).expect_err("missing condition");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("no conditional branch semantics")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: block 0 at 0x1000 has two CFG successors but no conditional branch semantics"
        );
    }

    #[test]
    fn test_block_terminator_pc_update_ite_mismatch_fails_strict() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1004, 0x1020],
            is_return: false,
        };
        cfg.add_block(block.clone());
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let pc_update = Effect::PcUpdate {
            value: Formula::Ite(
                Box::new(Formula::Var("take_branch".into(), trust_types::Sort::Bool)),
                Box::new(Formula::BitVec { value: 0x1030, width: 64 }),
                Box::new(Formula::BitVec { value: 0x1004, width: 64 }),
            ),
        };
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[pc_update], &state)
            .expect_err("mismatched PC ITE destinations should fail");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("do not match recovered CFG")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: block 0 at 0x1000 final PC ITE destinations do not match recovered CFG: target 0x1030 vs 0x1020, fallthrough 0x1004 vs 0x1004"
        );
    }

    #[test]
    fn test_block_terminator_too_many_successors_is_unrepresentable_cfg() {
        let cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010, 0x1020, 0x1030],
            is_return: false,
        };
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state)
            .expect_err("three successors are not representable");
        assert!(matches!(
            &err,
            LiftError::UnrepresentableCfg {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("has 3 CFG successors")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: block 0 at 0x1000 has 3 CFG successors; strict semantic lifting only supports 0, 1, or 2"
        );
    }

    #[test]
    fn test_block_terminator_last_call_without_successor_fails_closed() {
        let cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x94000040, 0x1000)], // BL #0x100
            successors: vec![],
            is_return: false,
        };
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state)
            .expect_err("last call without a boundary summary must fail closed");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow { message, .. }
                if message.contains("external Call target without a boundary summary")
        ));
    }

    #[test]
    fn test_block_terminator_indirect_call_fails_closed() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0xD63F0100, 0x1000)], // BLR X8
            successors: vec![0x1004],
            is_return: false,
        };
        cfg.add_block(block.clone());
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state)
            .expect_err("indirect calls are unresolved control flow in strict mode");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("unresolved Call target")
        ));
    }

    #[test]
    fn test_return_block_with_indirect_call_fails_closed() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![
                decode_aarch64(0xD63F0100, 0x1000), // BLR X8
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            successors: vec![],
            is_return: true,
        };
        cfg.add_block(block.clone());
        let state = MachineState::symbolic();

        let err = block_terminator(&block, &cfg, &[], &state)
            .expect_err("return blocks must still reject unresolved indirect calls");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("unresolved Call target")
        ));
    }

    #[test]
    fn test_lift_direct_external_branch_fails_closed() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x14000040, 0x1000)], // B #0x100 -> 0x1100
            successors: vec![],
            is_return: false,
        });

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("direct external branch must fail without a boundary summary");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow { message, .. }
                if message.contains("external DirectBranch target without a boundary summary")
        ));
    }

    #[test]
    fn test_lift_mixed_conditional_external_target_fails_closed() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0xB4000080, 0x1000)], // CBZ X0, #0x10 -> 0x1010
            successors: vec![0x1004],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![decode_aarch64(0xD65F03C0, 0x1004)], // RET
            successors: vec![],
            is_return: true,
        });

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("mixed conditional external target must fail without a boundary summary");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow { message, .. }
                if message.contains("external ConditionalTrue target without a boundary summary")
        ));
    }

    #[test]
    fn test_effect_regwrite_to_stmt() {
        let layout = LocalLayout::standard();
        let formula = trust_types::Formula::BitVec { value: 42, width: 64 };
        let effect = Effect::RegWrite { index: 5, width: 64, value: formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("RegWrite should lift");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.gpr(5));
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Uint(42, 64))) => {}
                    _ => panic!("expected Uint(42, 64), got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_zr_write_is_nop() {
        let layout = LocalLayout::standard();
        let effect = Effect::RegWrite {
            index: 31,
            width: 64,
            value: trust_types::Formula::BitVec { value: 0, width: 64 },
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("ZR write should lift");
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Statement::Nop));
    }

    /// Trust: #573 — x86_64 has 16 GPRs; index >= 16 is a Nop.
    #[test]
    fn test_effect_regwrite_x86_64_out_of_range_is_nop() {
        let layout = LocalLayout::x86_64();
        let effect = Effect::RegWrite {
            index: 16,
            width: 64,
            value: trust_types::Formula::BitVec { value: 0, width: 64 },
        };
        let stmts =
            effect_to_stmts(&effect, &layout, 0x1000).expect("out-of-range write should lift");
        assert_eq!(stmts.len(), 1);
        assert!(matches!(stmts[0], Statement::Nop));
    }

    /// Trust: #573 — x86_64 GPR index 15 (R15) should produce a valid Assign.
    #[test]
    fn test_effect_regwrite_x86_64_r15() {
        let layout = LocalLayout::x86_64();
        let effect = Effect::RegWrite {
            index: 15,
            width: 64,
            value: trust_types::Formula::BitVec { value: 99, width: 64 },
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x1000).expect("R15 write should lift");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, .. } => {
                assert_eq!(place.local, layout.gpr(15));
            }
            _ => panic!("expected Assign for R15"),
        }
    }

    #[test]
    fn test_effect_regwrite_symbolic_formula_preserved() {
        let layout = LocalLayout::standard();
        let sym_formula = Formula::BvAdd(
            Box::new(Formula::Var("X1".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::Var("X2".into(), trust_types::Sort::BitVec(64))),
            64,
        );
        let effect = Effect::RegWrite { index: 0, width: 64, value: sym_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x2000).expect("symbolic RegWrite");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.gpr(0));
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &sym_formula),
                    _ => panic!("expected Symbolic operand, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_sp_write_carries_formula() {
        let layout = LocalLayout::standard();
        let sp_formula = Formula::BvSub(
            Box::new(Formula::Var("SP".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 16, width: 64 }),
            64,
        );
        let effect = Effect::SpWrite { value: sp_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x3000).expect("SP write");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.sp_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &sp_formula),
                    _ => panic!("expected Symbolic operand, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_flag_update_carries_formulas() {
        let layout = LocalLayout::standard();
        let n_formula = Formula::BvSLt(
            Box::new(Formula::Var("result".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
            64,
        );
        let z_formula = Formula::Eq(
            Box::new(Formula::Var("result".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0, width: 64 }),
        );
        let effect = Effect::FlagUpdate {
            n: n_formula.clone(),
            z: z_formula.clone(),
            c: Formula::Bool(false),
            v: Formula::Bool(false),
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x4000).expect("flag update");
        assert_eq!(stmts.len(), 4);

        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_n);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &n_formula),
                    _ => panic!("expected Symbolic for N flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for N flag"),
        }

        match &stmts[1] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_z);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &z_formula),
                    _ => panic!("expected Symbolic for Z flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for Z flag"),
        }

        match &stmts[2] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.flag_c);
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Bool(false))) => {}
                    _ => panic!("expected Bool(false) for C flag, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign for C flag"),
        }
    }

    #[test]
    fn test_effect_mem_write_carries_formulas() {
        let layout = LocalLayout::standard();
        let addr_formula = Formula::Var("addr".into(), trust_types::Sort::BitVec(64));
        let val_formula = Formula::Var("val".into(), trust_types::Sort::BitVec(64));
        let effect = Effect::MemWrite {
            address: addr_formula.clone(),
            value: val_formula.clone(),
            width_bytes: 8,
        };
        let stmts = effect_to_stmts(&effect, &layout, 0x5000).expect("memory write");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.mem_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(Formula::Store(_, addr, val))) => {
                        assert!(matches!(
                            addr.as_ref(),
                            Formula::BvAdd(base, offset, 64)
                                if base.as_ref() == &addr_formula
                                    && matches!(offset.as_ref(), Formula::BitVec { value: 7, width: 64 })
                        ));
                        assert!(matches!(
                            val.as_ref(),
                            Formula::BvExtract { inner, high: 63, low: 56 }
                                if inner.as_ref() == &val_formula
                        ));
                    }
                    _ => panic!("expected Symbolic(Store(...)), got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_pc_update_carries_formula() {
        let layout = LocalLayout::standard();
        let pc_formula = Formula::BvAdd(
            Box::new(Formula::Var("PC".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        let effect = Effect::PcUpdate { value: pc_formula.clone() };
        let stmts = effect_to_stmts(&effect, &layout, 0x6000).expect("PC update");
        assert_eq!(stmts.len(), 1);
        match &stmts[0] {
            Statement::Assign { place, rvalue, .. } => {
                assert_eq!(place.local, layout.pc_local);
                match rvalue {
                    Rvalue::Use(Operand::Symbolic(f)) => assert_eq!(f, &pc_formula),
                    _ => panic!("expected Symbolic for PC update, got: {rvalue:?}"),
                }
            }
            _ => panic!("expected Assign"),
        }
    }

    #[test]
    fn test_effect_fp_reg_write_uses_structured_unsupported_effect() {
        let layout = LocalLayout::standard();
        let effect = Effect::FpRegWrite {
            index: 1,
            width: 128,
            value: Formula::BitVec { value: 0, width: 128 },
        };

        let err = effect_to_stmts(&effect, &layout, 0x7000)
            .expect_err("FP writes are not representable in the current layout");
        assert!(matches!(
            &err,
            LiftError::UnsupportedEffect {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("unsupported FP register write effect")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: unsupported FP register write effect at binary:0x7000: V1 width 128; no TrustIr FP local layout is available"
        );
    }

    #[test]
    fn test_memory_access_fact_classifies_stack_relative_address() {
        let insn = decode_x86_64(&[0x55], 0x401000); // PUSH RBP
        let address = Formula::BvSub(
            Box::new(Formula::Var("SP".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 8, width: 64 }),
            64,
        );
        let effect = Effect::MemWrite {
            address,
            value: Formula::BitVec { value: 0, width: 64 },
            width_bytes: 8,
        };

        let fact = memory_access_fact(
            0x401000,
            &insn,
            &effect,
            MemoryRegionHints::text(0x401000, 0x100),
            None,
        )
        .expect("memory fact");

        assert_eq!(fact.region, MemoryRegionKind::Stack);
        assert_eq!(fact.base_object.as_deref(), Some("SP"));
        assert_eq!(fact.offset, Some(Formula::BitVec { value: -8, width: 64 }));
        assert_eq!(fact.provenance.as_deref(), Some("stack-relative address rooted at SP"));
    }

    #[test]
    fn test_memory_access_fact_keeps_dynamic_stack_index_unknown() {
        let insn = decode_x86_64(&[0x55], 0x401000);
        let address = Formula::BvAdd(
            Box::new(Formula::Var("SP".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::Var("X0".into(), trust_types::Sort::BitVec(64))),
            64,
        );
        let effect = Effect::MemRead { address, width_bytes: 8 };

        let fact = memory_access_fact(
            0x401000,
            &insn,
            &effect,
            MemoryRegionHints::text(0x401000, 0x100),
            None,
        )
        .expect("memory fact");

        assert_eq!(fact.region, MemoryRegionKind::Unknown);
        assert!(fact.base_object.is_none());
        assert!(fact.provenance.is_none());
    }

    #[test]
    fn test_memory_access_fact_provenance_classifies_pc_relative_text_address_as_global() {
        let insn = decode_x86_64(&[0x48, 0x8B, 0x05, 0, 0, 0, 0], 0x401000);
        let address = Formula::BvAdd(
            Box::new(Formula::Var("PC".into(), trust_types::Sort::BitVec(64))),
            Box::new(Formula::BitVec { value: 0x20, width: 64 }),
            64,
        );
        let effect = Effect::MemRead { address, width_bytes: 8 };

        let fact = memory_access_fact(
            0x401000,
            &insn,
            &effect,
            MemoryRegionHints::text(0x401000, 0x100),
            None,
        )
        .expect("memory fact");

        assert_eq!(fact.origin.instruction_address, 0x401000);
        assert_eq!(fact.origin.instruction_size, Some(7));
        assert_eq!(fact.origin.encoding, Some(insn.encoding));
        assert_eq!(fact.origin.instruction_bytes, vec![0x48, 0x8b, 0x05, 0, 0, 0, 0]);
        assert_eq!(fact.region, MemoryRegionKind::Global);
        assert_eq!(fact.base_object.as_deref(), Some(".text"));
        assert_eq!(fact.offset, Some(Formula::BitVec { value: 0x20, width: 64 }));
        assert_eq!(fact.extent, Some(0x100));
        assert_eq!(fact.provenance.as_deref(), Some("loader text-section address"));
    }

    #[test]
    fn test_memory_access_fact_aarch64_origin_preserves_instruction_provenance() {
        let insn = decode_aarch64(0xF9000020, 0x401008); // STR X0, [X1]
        let effect = Effect::MemWrite {
            address: Formula::Var("X1".into(), trust_types::Sort::BitVec(64)),
            value: Formula::Var("X0".into(), trust_types::Sort::BitVec(64)),
            width_bytes: 8,
        };

        let fact = memory_access_fact(0x401000, &insn, &effect, MemoryRegionHints::default(), None)
            .expect("memory fact");

        assert_eq!(fact.origin.function_entry, Some(0x401000));
        assert_eq!(fact.origin.instruction_address, 0x401008);
        assert_eq!(fact.origin.instruction_size, Some(4));
        assert_eq!(fact.origin.encoding, Some(0xF9000020));
        assert_eq!(fact.origin.instruction_bytes, 0xF9000020u32.to_le_bytes().to_vec());
    }

    #[test]
    fn test_memory_access_fact_aarch64_ldar_ldaxr_preserve_load_provenance() {
        for (encoding, opcode, base) in [
            (0xC8DFFC20, Opcode::Ldar, "X1"),  // LDAR X0, [X1]
            (0xC85FFC20, Opcode::Ldaxr, "X1"), // LDAXR X0, [X1]
        ] {
            let insn = decode_aarch64(encoding, 0x401008);
            assert_eq!(insn.opcode, opcode);
            assert!(insn.is_load(), "{opcode:?} should stay classified as a load");
            assert!(!insn.is_store(), "{opcode:?} should not be classified as a store");

            let effect = Effect::MemRead {
                address: Formula::Var(base.into(), trust_types::Sort::BitVec(64)),
                width_bytes: 8,
            };
            let fact =
                memory_access_fact(0x401000, &insn, &effect, MemoryRegionHints::default(), None)
                    .expect("memory fact");

            assert_eq!(fact.kind, MemoryAccessKind::Read);
            assert_eq!(fact.width_bytes, 8);
            assert_eq!(fact.origin.function_entry, Some(0x401000));
            assert_eq!(fact.origin.instruction_address, 0x401008);
            assert_eq!(fact.origin.instruction_size, Some(4));
            assert_eq!(fact.origin.encoding, Some(encoding));
            assert_eq!(fact.origin.instruction_bytes, encoding.to_le_bytes().to_vec());
            assert_eq!(fact.address, Formula::Var(base.into(), trust_types::Sort::BitVec(64)));
            assert_eq!(fact.region, MemoryRegionKind::Unknown);
            assert!(fact.base_object.is_none());
        }
    }

    #[test]
    fn test_memory_access_fact_keeps_unbacked_absolute_address_unknown() {
        let insn = decode_x86_64(&[0x48, 0x8B, 0x05, 0, 0, 0, 0], 0x401000);
        let effect = Effect::MemRead {
            address: Formula::BitVec { value: 0x500000, width: 64 },
            width_bytes: 8,
        };

        let fact = memory_access_fact(
            0x401000,
            &insn,
            &effect,
            MemoryRegionHints::text(0x401000, 0x100),
            None,
        )
        .expect("memory fact");

        assert_eq!(fact.region, MemoryRegionKind::Unknown);
        assert!(fact.base_object.is_none());
    }

    // ====================================================================
    // Trust: #573 — End-to-end x86_64 semantic lifting tests
    // ====================================================================

    /// Helper: decode an x86_64 instruction from a byte slice.
    fn decode_x86_64(bytes: &[u8], addr: u64) -> trust_disasm::Instruction {
        trust_disasm::decode_x86_64(bytes, addr).expect("x86_64 decode should succeed")
    }

    /// Helper: decode an AArch64 instruction from a u32 encoding.
    fn decode_aarch64(encoding: u32, addr: u64) -> trust_disasm::Instruction {
        trust_disasm::decode_aarch64(&encoding.to_le_bytes(), addr)
            .expect("AArch64 decode should succeed")
    }

    fn aarch64_fallthrough_opcode(
        encoding: u32,
        addr: u64,
        opcode: Opcode,
    ) -> trust_disasm::Instruction {
        let mut insn = decode_aarch64(0xD503_201F, addr); // NOP shell; operands are not read.
        insn.encoding = encoding;
        insn.bytes = encoding.to_le_bytes().to_vec();
        insn.opcode = opcode;
        insn
    }

    /// Build a CFG with one entry block containing the given instructions.
    fn cfg_with_block(instructions: Vec<trust_disasm::Instruction>, is_return: bool) -> Cfg {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions,
            successors: vec![],
            is_return,
        });
        cfg
    }

    fn has_assign_to(block: &TrustIrBlock, local: usize) -> bool {
        block
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == local))
    }

    fn has_assign_to_with(
        block: &TrustIrBlock,
        local: usize,
        predicate: impl Fn(&Rvalue) -> bool,
    ) -> bool {
        block.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, rvalue, .. } if place.local == local && predicate(rvalue))
        })
    }

    fn assign_count_to(block: &TrustIrBlock, local: usize) -> usize {
        block
            .stmts
            .iter()
            .filter(|stmt| matches!(stmt, Statement::Assign { place, .. } if place.local == local))
            .count()
    }

    fn has_pc_assign_to(
        block: &TrustIrBlock,
        pc_local: usize,
        insn_addr: u64,
        expected_next_pc: u64,
    ) -> bool {
        block.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    span,
                } if place.local == pc_local
                    && span.binary_address_value() == Some(insn_addr)
                    && constant_pc_value(formula) == Some(expected_next_pc)
            )
        })
    }

    fn pc_assign_formula(block: &TrustIrBlock, pc_local: usize) -> &Formula {
        block
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    ..
                } if place.local == pc_local => Some(formula),
                _ => None,
            })
            .expect("block should assign symbolic PC")
    }

    fn symbolic_formula(operand: &Operand) -> &Formula {
        match operand {
            Operand::Symbolic(formula) => formula,
            other => panic!("expected symbolic operand, got {other:?}"),
        }
    }

    fn formula_is_var(formula: &Formula, expected: &str) -> bool {
        matches!(formula, Formula::Var(name, _) if name == expected)
    }

    fn formula_is_low_extract(formula: &Formula, expected: &str, width: u32) -> bool {
        matches!(
            formula,
            Formula::BvExtract { inner, high, low }
                if *high == width - 1 && *low == 0 && formula_is_var(inner, expected)
        )
    }

    fn formula_is_uxtw64(formula: &Formula, expected: &str) -> bool {
        matches!(
            formula,
            Formula::BvZeroExt(inner, 32) if formula_is_low_extract(inner, expected, 32)
        )
    }

    fn formula_is_shifted_uxtw64(formula: &Formula, expected: &str, shift: u8) -> bool {
        matches!(
            formula,
            Formula::BvShl(value, amount, 64)
                if formula_is_uxtw64(value, expected)
                    && matches!(
                        amount.as_ref(),
                        Formula::BitVec { value, width: 64 } if *value == i128::from(shift)
                    )
        )
    }

    fn formula_contains_bv_extract(formula: &Formula) -> bool {
        matches!(formula, Formula::BvExtract { .. })
            || formula.children().into_iter().any(formula_contains_bv_extract)
    }

    fn formula_contains_bv_mul(formula: &Formula) -> bool {
        matches!(formula, Formula::BvMul(_, _, _))
            || formula.children().into_iter().any(formula_contains_bv_mul)
    }

    fn formula_contains_bv_sub(formula: &Formula) -> bool {
        matches!(formula, Formula::BvSub(_, _, _))
            || formula.children().into_iter().any(formula_contains_bv_sub)
    }

    fn formula_contains_bv_sign_ext(formula: &Formula) -> bool {
        matches!(formula, Formula::BvSignExt(_, _))
            || formula.children().into_iter().any(formula_contains_bv_sign_ext)
    }

    fn assert_zero_compare_condition(formula: &Formula, reg_name: &str, width: u32, negated: bool) {
        let formula = if negated {
            match formula {
                Formula::Not(inner) => inner.as_ref(),
                other => panic!("expected negated zero compare, got {other:?}"),
            }
        } else {
            formula
        };

        match formula {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Formula::Var(name, _) if name == reg_name));
                assert!(matches!(
                    rhs.as_ref(),
                    Formula::BitVec { value: 0, width: actual_width } if *actual_width == width
                ));
            }
            other => panic!("expected exact zero compare, got {other:?}"),
        }
    }

    fn assert_bit_test_condition(formula: &Formula, reg_name: &str, bit: u32, negated: bool) {
        let formula = if negated {
            match formula {
                Formula::Not(inner) => inner.as_ref(),
                other => panic!("expected negated bit test, got {other:?}"),
            }
        } else {
            formula
        };

        match formula {
            Formula::Eq(lhs, rhs) => {
                assert!(matches!(
                    lhs.as_ref(),
                    Formula::BvExtract { inner, high, low }
                        if *high == bit
                            && *low == bit
                            && matches!(inner.as_ref(), Formula::Var(name, _) if name == reg_name)
                ));
                assert!(matches!(rhs.as_ref(), Formula::BitVec { value: 0, width: 1 }));
            }
            other => panic!("expected exact bit test, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_ret_only() {
        let cfg = cfg_with_block(
            vec![decode_aarch64(0xD65F03C0, 0x1000)], // RET
            true,
        );

        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("AArch64 RET should lift");

        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 39);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to(&blocks[0], layout.pc_local),
            "RET should preserve its PC update formula before the Return terminator"
        );
    }

    #[test]
    fn test_aarch64_minimal_ret_noop_hint_slice_has_empty_unsupported_ledger() {
        let instructions = vec![
            decode_aarch64(0xD503201F, 0x1000), // NOP
            decode_aarch64(0xD503203F, 0x1004), // YIELD
            decode_aarch64(0xD503209F, 0x1008), // SEV
            decode_aarch64(0xD50320BF, 0x100C), // SEVL
            decode_aarch64(0xF9800020, 0x1010), // PRFM #0, [X1]
            decode_aarch64(0xD65F03C0, 0x1014), // RET X30
        ];
        for insn in &instructions {
            let boundary = aarch64_empty_unsupported_ledger_boundary(insn)
                .expect("fixture instruction must be in the exact empty-ledger boundary");
            assert!(boundary.contains("exact-empty-ledger-boundary"), "{boundary}");
        }
        let cfg = cfg_with_block(instructions, true);

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("minimal RET/no-op/hint slice should lift proof-clean");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(facts.is_empty(), "no-op/hint slice must not synthesize memory facts");
        assert!(
            unsupported.is_empty(),
            "minimal RET/no-op/hint slice must carry an empty unsupported ledger"
        );
        assert!(
            has_assign_to(&blocks[0], layout.pc_local),
            "no-op/hint instructions should keep explicit PC advance provenance"
        );
    }

    #[test]
    fn test_aarch64_empty_ledger_boundary_excludes_proof_blockers() {
        let excluded = [
            (0xD503205F, Opcode::Wfe, "wait/event state"),
            (0xD503207F, Opcode::Wfi, "interrupt state"),
            (0xD5033B9F, Opcode::Dmb, "ordering boundary"),
            (0xD5033FDF, Opcode::Isb, "instruction synchronization boundary"),
            (0xD503305F, Opcode::Clrex, "exclusive-monitor clear"),
            (0xC8DFFC20, Opcode::Ldar, "acquire ordering"),
            (0xC85FFC20, Opcode::Ldaxr, "exclusive monitor"),
            (0xD65F0200, Opcode::Ret, "non-X30 return target"),
        ];

        for (encoding, opcode, reason) in excluded {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.opcode, opcode, "{reason}");
            assert!(
                aarch64_empty_unsupported_ledger_boundary(&insn).is_none(),
                "{reason} must remain outside the exact empty-ledger boundary"
            );
        }
    }

    #[test]
    fn test_aarch64_selected_stlr_ldar_slice_has_empty_unsupported_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xC89FFC20, 0x1000), // STLR X0, [X1]
                decode_aarch64(0xC8DFFC20, 0x1004), // LDAR X0, [X1]
                decode_aarch64(0xD65F03C0, 0x1008), // RET X30
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("selected STLR/LDAR ordering slice should lift with reviewed evidence");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(unsupported.is_empty(), "accepted AArch64 slice must have an empty ledger");
        assert_eq!(facts.len(), 2, "accepted slice should preserve both scalar memory facts");
        assert_eq!(facts[0].kind, MemoryAccessKind::Write);
        assert_eq!(facts[1].kind, MemoryAccessKind::Read);
        assert_eq!(facts[0].address, facts[1].address, "STLR/LDAR pair must bind one location");
        assert!(
            facts[0].provenance.as_deref().is_some_and(|provenance| {
                provenance.contains("accepted-slice:aarch64.release_acquire")
                    && provenance.contains("role=release")
                    && provenance.contains("release ordering event")
                    && provenance.contains(&format!(
                        "evidence_schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}"
                    ))
                    && provenance.contains("evidence_id=aarch64-ra:sha256:")
                    && provenance.contains("selected_image_digest=sha256:")
                    && provenance.contains("instruction_provenance_digest=sha256:")
                    && provenance.contains("memory_access_digest=sha256:")
                    && provenance.contains(&format!(
                        "artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}"
                    ))
                    && provenance.contains(&format!(
                        "artifact_row_type={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_TYPE}"
                    ))
                    && provenance.contains("artifact_row_status=accepted")
                    && provenance.contains("opcode=Stlr")
                    && provenance.contains("ordering=Release")
                    && provenance.contains("ordering_event=release ordering event")
                    && provenance.contains("unsupported_ledger_boundary=explicit-empty")
                    && provenance.contains("unsupported_ledger_records=0")
                    && provenance.contains("exclusive_monitor=None")
                    && provenance.contains("exclusive_monitor_witness=not-applicable-reviewed")
                    && provenance.contains("store_conditional_status=not-applicable-reviewed")
                    && provenance.contains("synchronization_edge=absent-reviewed")
                    && provenance.contains("happens_before_witness=absent-reviewed")
                    && provenance.contains("thread_identity=absent-reviewed")
                    && provenance.contains(&format!(
                        "reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}"
                    ))
                    && provenance.contains("happens-before witness absent-reviewed")
                    && provenance.contains(&format!(
                        "aarch64_ordering_monitor_evidence_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}"
                    ))
                    && provenance.contains("aarch64_ordering_monitor_evidence_status=accepted")
                    && provenance.contains("aarch64_ordering_monitor_evidence_opcode=Stlr")
                    && provenance.contains("aarch64_ordering_monitor_evidence_ordering=Release")
                    && provenance
                        .contains("aarch64_ordering_monitor_evidence_exclusive_monitor=None")
                    && provenance.contains("aarch64_ordering_monitor_evidence_digest=sha256:")
                    && provenance.contains("aarch64_ordering_monitor_evidence_blockers=[]")
                    && provenance.contains("release_transcript_consumed=true")
                    && provenance.contains("release_transcript_digest=sha256:")
                    && provenance.contains("no FP/SIMD/syscall/trap/exception claim")
            }),
            "release fact must carry reviewed accepted-boundary provenance: {:?}",
            facts[0].provenance
        );
        assert!(
            facts[1].provenance.as_deref().is_some_and(|provenance| {
                provenance.contains("accepted-slice:aarch64.release_acquire")
                    && provenance.contains("role=acquire")
                    && provenance.contains("acquire ordering event")
                    && provenance.contains(&format!(
                        "evidence_schema={AARCH64_RELEASE_ACQUIRE_EVIDENCE_SCHEMA}"
                    ))
                    && provenance.contains("evidence_id=aarch64-ra:sha256:")
                    && provenance.contains("selected_image_digest=sha256:")
                    && provenance.contains("instruction_provenance_digest=sha256:")
                    && provenance.contains("memory_access_digest=sha256:")
                    && provenance.contains(&format!(
                        "artifact_row_schema={AARCH64_ORDERING_MONITOR_EVIDENCE_ROW_SCHEMA}"
                    ))
                    && provenance.contains("artifact_row_status=accepted")
                    && provenance.contains("opcode=Ldar")
                    && provenance.contains("ordering=Acquire")
                    && provenance.contains("ordering_event=acquire ordering event")
                    && provenance.contains("unsupported_ledger_boundary=explicit-empty")
                    && provenance.contains("unsupported_ledger_records=0")
                    && provenance.contains("exclusive_monitor=None")
                    && provenance.contains("exclusive_monitor_witness=not-applicable-reviewed")
                    && provenance.contains("store_conditional_status=not-applicable-reviewed")
                    && provenance.contains("synchronization_edge=absent-reviewed")
                    && provenance.contains("happens_before_witness=absent-reviewed")
                    && provenance.contains("thread_identity=absent-reviewed")
                    && provenance.contains(&format!(
                        "reviewed_unsupported_absence={AARCH64_REVIEWED_UNSUPPORTED_ABSENCE}"
                    ))
                    && provenance.contains("synchronization edge absent-reviewed")
                    && provenance.contains("aarch64_ordering_monitor_evidence_status=accepted")
                    && provenance.contains("aarch64_ordering_monitor_evidence_opcode=Ldar")
                    && provenance.contains("aarch64_ordering_monitor_evidence_ordering=Acquire")
                    && provenance
                        .contains("aarch64_ordering_monitor_evidence_exclusive_monitor=None")
                    && provenance.contains("aarch64_ordering_monitor_evidence_digest=sha256:")
                    && provenance.contains("release_transcript_consumed=true")
                    && provenance.contains("release_transcript_digest=sha256:")
                    && provenance.contains("no FP/SIMD/syscall/trap/exception claim")
            }),
            "acquire fact must carry reviewed accepted-boundary provenance: {:?}",
            facts[1].provenance
        );

        let selected_image_digest =
            aarch64_release_acquire_selected_image_digest(0x1000, &cfg.blocks[0]);
        let release_instruction_digest = aarch64_instruction_provenance_digest(&facts[0].origin);
        let release_memory_digest = aarch64_memory_access_digest(&facts[0]);
        let release_evidence_id = aarch64_release_acquire_evidence_id(
            Aarch64AcceptedOrderingRole::Release,
            &selected_image_digest,
            &release_instruction_digest,
            &release_memory_digest,
        );
        let acquire_evidence_id = aarch64_release_acquire_evidence_id(
            Aarch64AcceptedOrderingRole::Acquire,
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&facts[1].origin),
            &aarch64_memory_access_digest(&facts[1]),
        );
        assert!(
            facts[0].provenance.as_deref().is_some_and(
                |provenance| provenance.contains(&format!("evidence_id={release_evidence_id}"))
            ),
            "release provenance must bind the stable evidence id"
        );
        assert!(
            facts[1].provenance.as_deref().is_some_and(
                |provenance| provenance.contains(&format!("evidence_id={acquire_evidence_id}"))
            ),
            "acquire provenance must bind the stable evidence id"
        );

        let (_, _, repeat_facts, _) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("repeat selected slice lift should be stable");
        let repeat_release_id = aarch64_release_acquire_evidence_id(
            Aarch64AcceptedOrderingRole::Release,
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&repeat_facts[0].origin),
            &aarch64_memory_access_digest(&repeat_facts[0]),
        );
        assert_eq!(
            release_evidence_id, repeat_release_id,
            "normalized selected-slice evidence id must be stable"
        );

        let mut stale_release = facts[0].clone();
        stale_release.origin.instruction_address += 4;
        let stale_release_id = aarch64_release_acquire_evidence_id(
            Aarch64AcceptedOrderingRole::Release,
            &selected_image_digest,
            &aarch64_instruction_provenance_digest(&stale_release.origin),
            &aarch64_memory_access_digest(&stale_release),
        );
        assert_ne!(
            release_evidence_id, stale_release_id,
            "stale instruction provenance must change the evidence id"
        );
        assert!(has_pc_assign_to(&blocks[0], layout.pc_local, 0x1000, 0x1004));
        assert!(has_pc_assign_to(&blocks[0], layout.pc_local, 0x1004, 0x1008));
    }

    #[test]
    fn test_aarch64_selected_stlr_ldar_boundary_requires_exact_shape() {
        let mismatched_address = cfg_with_block(
            vec![
                decode_aarch64(0xC89FFC20, 0x1000), // STLR X0, [X1]
                decode_aarch64(0xC8DFFC40, 0x1004), // LDAR X0, [X2]
                decode_aarch64(0xD65F03C0, 0x1008), // RET X30
            ],
            true,
        );
        let err = lift_cfg_semantic_with_facts_and_ledger(&mismatched_address, LiftArch::Aarch64)
            .expect_err("mismatched STLR/LDAR location must remain fail-closed");
        assert!(
            err.to_string()
                .contains("AArch64 atomic memory-order semantics are unsupported fail-closed"),
            "{err}"
        );

        let exclusive = cfg_with_block(
            vec![
                decode_aarch64(0xC85FFC20, 0x1000), // LDAXR X0, [X1]
                decode_aarch64(0xC802FC20, 0x1004), // STLXR W2, X0, [X1]
                decode_aarch64(0xD65F03C0, 0x1008), // RET X30
            ],
            true,
        );
        let err = lift_cfg_semantic_with_facts_and_ledger(&exclusive, LiftArch::Aarch64)
            .expect_err("exclusive monitor pair needs status/monitor witnesses");
        assert!(
            err.to_string().contains(
                "AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed"
            ),
            "{err}"
        );
    }

    #[test]
    fn test_aarch64_lift_non_link_register_return_fails_closed() {
        let cfg = cfg_with_block(
            vec![decode_aarch64(0xD65F0200, 0x1000)], // RET X16
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("RET X16 needs a replayed return-target witness before proof lifting");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 indirect return boundary")
                && message.contains("RET X16")
                && message.contains("proof-grade replay")
                && message.contains("unsupported-ledger")
        ));
    }

    #[test]
    fn test_aarch64_lift_minimal_move_add_sub_fixture() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD2800020, 0x1000), // MOVZ X0, #1
                decode_aarch64(0x91000800, 0x1004), // ADD X0, X0, #2
                decode_aarch64(0xD1000401, 0x1008), // SUB X1, X0, #1
                decode_aarch64(0xD65F03C0, 0x100C), // RET
            ],
            true,
        );

        let (blocks, layout) = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect("minimal AArch64 arithmetic fixture should lift");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(0), |rvalue| matches!(
                rvalue,
                Rvalue::Use(Operand::Constant(ConstValue::Uint(1, 64)))
            )),
            "MOVZ X0, #1 should write the concrete value 1 to X0"
        );
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(0), |rvalue| matches!(
                rvalue,
                Rvalue::Use(Operand::Symbolic(Formula::BvAdd(_, _, 64)))
            )),
            "ADD X0, X0, #2 should preserve an add formula"
        );
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(1), |rvalue| matches!(
                rvalue,
                Rvalue::Use(Operand::Symbolic(Formula::BvSub(_, _, 64)))
            )),
            "SUB X1, X0, #1 should preserve a sub formula"
        );
    }

    #[test]
    fn test_aarch64_lift_movn_fixture_without_unsupported_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x92800000, 0x1000), // MOVN X0, #0
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("MOVN should lift as supported move-wide scalar semantics");

        assert!(unsupported.is_empty());
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(0), |rvalue| matches!(
                rvalue,
                Rvalue::Use(Operand::Symbolic(Formula::BvNot(inner, 64)))
                    if matches!(inner.as_ref(), Formula::BitVec { value: 0, width: 64 })
            )),
            "MOVN X0, #0 should write the bitwise-not formula for all-ones"
        );
    }

    #[test]
    fn test_aarch64_lift_adr_fixture_writes_exact_pc_relative_address_without_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x10000080, 0x1000), // ADR X0, #0x10 -> 0x1010
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ADR should lift as exact PC-relative address dataflow");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(facts.is_empty(), "ADR computes an address but must not record a memory access");
        assert!(unsupported.is_empty(), "ADR exact scalar dataflow should not use the ledger");
        assert!(
            blocks[0].stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign { place, rvalue, span }
                        if place.local == layout.gpr(0)
                            && matches!(
                                rvalue,
                                Rvalue::Use(Operand::Constant(ConstValue::Uint(0x1010, 64)))
                            )
                            && span.binary_address_value() == Some(0x1000)
                )
            }),
            "ADR should write the decoded PC-relative address to X0 with instruction provenance"
        );
        assert!(
            blocks[0].stmts.iter().any(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(lhs, rhs, 64))),
                    span,
                } => {
                    place.local == layout.pc_local
                        && matches!(lhs.as_ref(), Formula::BitVec { value: 0x1000, width: 64 })
                        && matches!(rhs.as_ref(), Formula::BitVec { value: 4, width: 64 })
                        && span.binary_address_value() == Some(0x1000)
                }
                _ => false,
            }),
            "ADR should still advance PC exactly from the instruction address"
        );
    }

    #[test]
    fn test_aarch64_lift_adrp_fixture_writes_exact_page_address_without_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xB0000000, 0x1000), // ADRP X0, #0x2000
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ADRP should lift as exact PC-relative page address dataflow");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(facts.is_empty(), "ADRP computes an address but must not record a memory access");
        assert!(unsupported.is_empty(), "ADRP exact scalar dataflow should not use the ledger");
        assert!(
            blocks[0].stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign { place, rvalue, span }
                        if place.local == layout.gpr(0)
                            && matches!(
                                rvalue,
                                Rvalue::Use(Operand::Constant(ConstValue::Uint(0x2000, 64)))
                            )
                            && span.binary_address_value() == Some(0x1000)
                )
            }),
            "ADRP should write the decoded page address to X0 with instruction provenance"
        );
        assert!(
            blocks[0].stmts.iter().any(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(lhs, rhs, 64))),
                    span,
                } => {
                    place.local == layout.pc_local
                        && matches!(lhs.as_ref(), Formula::BitVec { value: 0x1000, width: 64 })
                        && matches!(rhs.as_ref(), Formula::BitVec { value: 4, width: 64 })
                        && span.binary_address_value() == Some(0x1000)
                }
                _ => false,
            }),
            "ADRP should still advance PC exactly from the instruction address"
        );
    }

    #[test]
    fn test_aarch64_lift_adrp_ldr_unsigned_offset_preserves_materialized_global_provenance() {
        let adrp_encoding = 0xB0000008; // ADRP X8, #0x2000
        let ldr_encoding = 0xF9402100; // LDR X0, [X8, #0x40]
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(adrp_encoding, 0x1000),
                decode_aarch64(ldr_encoding, 0x1004),
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ADRP + unsigned-offset LDR should retain exact address provenance");

        assert!(unsupported.is_empty());
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(has_assign_to(&blocks[0], layout.gpr(0)), "LDR should assign X0");
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.kind, MemoryAccessKind::Read);
        assert_eq!(fact.width_bytes, 8);
        assert_eq!(fact.region, MemoryRegionKind::Global);
        assert_eq!(fact.base_object.as_deref(), Some("pc-relative"));
        assert_eq!(fact.offset, Some(Formula::BitVec { value: 0x2040, width: 64 }));
        assert_eq!(fact.provenance.as_deref(), Some("PC-relative memory address"));
        assert_eq!(fact.origin.function_entry, Some(0x1000));
        assert_eq!(fact.origin.instruction_address, 0x1004);
        assert_eq!(fact.origin.instruction_size, Some(4));
        assert_eq!(fact.origin.encoding, Some(ldr_encoding));
        assert_eq!(fact.origin.instruction_bytes, ldr_encoding.to_le_bytes().to_vec());
        assert_eq!(concrete_address(&fact.address, 0x1004).map(|addr| addr.address), Some(0x2040));
    }

    #[test]
    fn test_aarch64_lift_adrp_add_ldr_preserves_materialized_global_provenance() {
        let adrp_encoding = 0xB0000008; // ADRP X8, #0x2000
        let add_encoding = 0x91010108; // ADD X8, X8, #0x40
        let ldr_encoding = 0xF9400100; // LDR X0, [X8]
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(adrp_encoding, 0x1000),
                decode_aarch64(add_encoding, 0x1004),
                decode_aarch64(ldr_encoding, 0x1008),
                decode_aarch64(0xD65F03C0, 0x100C), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ADRP + ADD + LDR should retain exact address provenance");

        assert!(unsupported.is_empty());
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            blocks[0].stmts.iter().any(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(lhs, rhs, 64))),
                    span,
                } => {
                    place.local == layout.gpr(8)
                        && matches!(lhs.as_ref(), Formula::BitVec { value: 0x2000, width: 64 })
                        && matches!(rhs.as_ref(), Formula::BitVec { value: 0x40, width: 64 })
                        && span.binary_address_value() == Some(0x1004)
                }
                _ => false,
            }),
            "ADD should materialize the page offset while preserving instruction provenance"
        );
        assert!(has_assign_to(&blocks[0], layout.gpr(0)), "LDR should assign X0");
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.kind, MemoryAccessKind::Read);
        assert_eq!(fact.width_bytes, 8);
        assert_eq!(fact.region, MemoryRegionKind::Global);
        assert_eq!(fact.base_object.as_deref(), Some("pc-relative"));
        assert_eq!(fact.offset, Some(Formula::BitVec { value: 0x2040, width: 64 }));
        assert_eq!(fact.provenance.as_deref(), Some("PC-relative memory address"));
        assert_eq!(fact.origin.function_entry, Some(0x1000));
        assert_eq!(fact.origin.instruction_address, 0x1008);
        assert_eq!(fact.origin.instruction_size, Some(4));
        assert_eq!(fact.origin.encoding, Some(ldr_encoding));
        assert_eq!(fact.origin.instruction_bytes, ldr_encoding.to_le_bytes().to_vec());
        assert_eq!(concrete_address(&fact.address, 0x1008).map(|addr| addr.address), Some(0x2040));
    }

    #[test]
    fn test_aarch64_lift_add_extended_register_fixture_without_unsupported_ledger() {
        let encoding = 0x8B224020; // ADD X0, X1, W2, UXTW
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(encoding, 0x1000),
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ADD extended-register should lift exactly");

        assert!(facts.is_empty(), "ADD extended-register computes data, not a memory access");
        assert!(unsupported.is_empty());
        let add_formula = blocks[0]
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    span,
                } if place.local == layout.gpr(0)
                    && span.binary_address_value() == Some(0x1000) =>
                {
                    Some(formula)
                }
                _ => None,
            })
            .expect("ADD extended-register should assign X0 with instruction provenance");

        match add_formula {
            Formula::BvAdd(lhs, rhs, 64) => {
                assert!(formula_is_var(lhs, "X1"));
                assert!(formula_is_uxtw64(rhs, "X2"));
            }
            other => panic!("expected X1 + UXTW(W2) formula, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_ldr_register_offset_uxtw_preserves_exact_address_and_memory_provenance() {
        let encoding = 0xF8625820; // LDR X0, [X1, W2, UXTW #3]
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(encoding, 0x1000),
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("LDR register-offset with UXTW should lift exactly");

        assert!(unsupported.is_empty());
        assert!(has_assign_to(&blocks[0], layout.gpr(0)), "LDR should assign X0");
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.kind, MemoryAccessKind::Read);
        assert_eq!(fact.width_bytes, 8);
        assert_eq!(fact.origin.function_entry, Some(0x1000));
        assert_eq!(fact.origin.instruction_address, 0x1000);
        assert_eq!(fact.origin.instruction_size, Some(4));
        assert_eq!(fact.origin.encoding, Some(encoding));
        assert_eq!(fact.origin.instruction_bytes, encoding.to_le_bytes().to_vec());

        match &fact.address {
            Formula::BvAdd(base, index, 64) => {
                assert!(formula_is_var(base, "X1"));
                assert!(formula_is_shifted_uxtw64(index, "X2", 3));
            }
            other => panic!("expected X1 + (UXTW(W2) << 3) address formula, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_long_multiply_fixture_without_unsupported_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x9B220C20, 0x1000), // SMADDL X0, W1, W2, X3
                decode_aarch64(0x9BC600A4, 0x1004), // UMULH X4, X5, X6
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("AArch64 long multiply fixture should lift");

        assert!(unsupported.is_empty());
        assert!(has_assign_to_with(&blocks[0], layout.gpr(0), |rvalue| match rvalue {
            Rvalue::Use(Operand::Symbolic(formula)) => {
                formula_contains_bv_mul(formula) && formula_contains_bv_sign_ext(formula)
            }
            _ => false,
        }));
        assert!(has_assign_to_with(&blocks[0], layout.gpr(4), |rvalue| {
            matches!(
                rvalue,
                Rvalue::Use(Operand::Symbolic(Formula::BvExtract { high: 127, low: 64, .. }))
            )
        }));
    }

    #[test]
    fn test_aarch64_lift_stack_load_store_fixture_records_memory_facts() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xF90007E1, 0x1000), // STR X1, [SP, #8]
                decode_aarch64(0xF94007E2, 0x1004), // LDR X2, [SP, #8]
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, facts) = lift_cfg_semantic_with_facts(&cfg, LiftArch::Aarch64)
            .expect("AArch64 stack load/store fixture should lift");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to(&blocks[0], layout.mem_local),
            "STR should update the symbolic memory local"
        );
        assert!(has_assign_to(&blocks[0], layout.gpr(2)), "LDR should write X2");

        assert_eq!(facts.len(), 2);
        assert!(facts.iter().any(|fact| {
            fact.kind == MemoryAccessKind::Write
                && fact.width_bytes == 8
                && fact.region == MemoryRegionKind::Stack
                && fact.base_object.as_deref() == Some("SP")
                && fact.offset == Some(Formula::BitVec { value: 8, width: 64 })
        }));
        assert!(facts.iter().any(|fact| {
            fact.kind == MemoryAccessKind::Read
                && fact.width_bytes == 8
                && fact.region == MemoryRegionKind::Stack
                && fact.base_object.as_deref() == Some("SP")
                && fact.offset == Some(Formula::BitVec { value: 8, width: 64 })
        }));
    }

    #[test]
    fn test_aarch64_lift_narrow_load_store_fixture_preserves_access_widths() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x39400020, 0x1000), // LDRB W0, [X1]
                decode_aarch64(0x79000820, 0x1004), // STRH W0, [X1, #4]
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, facts) = lift_cfg_semantic_with_facts(&cfg, LiftArch::Aarch64)
            .expect("AArch64 narrow load/store fixture should lift");

        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(0), |rvalue| matches!(
                rvalue,
                Rvalue::Use(Operand::Symbolic(Formula::BvZeroExt(_, 32)))
            )),
            "LDRB W0 should zero-extend the byte load into W0"
        );
        assert_eq!(assign_count_to(&blocks[0], layout.mem_local), 1);
        assert!(
            facts
                .iter()
                .any(|fact| { fact.kind == MemoryAccessKind::Read && fact.width_bytes == 1 })
        );
        assert!(
            facts
                .iter()
                .any(|fact| { fact.kind == MemoryAccessKind::Write && fact.width_bytes == 2 })
        );
    }

    #[test]
    fn test_aarch64_lift_ldrsw_decompilation_json_preserves_memory_provenance() {
        let encoding = 0xB98007E0; // LDRSW X0, [SP, #4]
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(encoding, 0x1000),
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("supported AArch64 LDRSW stack load should lift");

        assert!(unsupported.is_empty());
        assert_eq!(facts.len(), 1);
        let fact = &facts[0];
        assert_eq!(fact.kind, MemoryAccessKind::Read);
        assert_eq!(fact.width_bytes, 4);
        assert_eq!(fact.region, MemoryRegionKind::Stack);
        assert_eq!(fact.base_object.as_deref(), Some("SP"));
        assert_eq!(fact.offset, Some(Formula::BitVec { value: 4, width: 64 }));
        assert_eq!(fact.provenance.as_deref(), Some("stack-relative address rooted at SP"));
        assert_eq!(fact.origin.instruction_address, 0x1000);
        assert_eq!(fact.origin.instruction_size, Some(4));
        assert_eq!(fact.origin.encoding, Some(encoding));
        assert_eq!(fact.origin.instruction_bytes, encoding.to_le_bytes().to_vec());

        let artifact = trust_types::DecompilationArtifact {
            binary: trust_types::BinaryArtifactMetadata {
                architecture: "AArch64".into(),
                entry_point: Some(0x1000),
                ..Default::default()
            },
            functions: vec![trust_types::DecompiledFunction {
                name: "aarch64_ldrsw".into(),
                entry: 0x1000,
                memory_accesses: facts.clone(),
                unsupported: unsupported.clone(),
                ..Default::default()
            }],
            memory_model: trust_types::BinaryMemoryModel {
                pointer_width_bits: Some(64),
                endianness: Endianness::Little,
                accesses: facts,
                ..Default::default()
            },
            unsupported,
            ..Default::default()
        };

        let json = serde_json::to_value(&artifact).expect("serialize decompilation artifact");
        let function_access = &json["functions"][0]["memory_accesses"][0];
        assert_eq!(function_access["kind"], "Read");
        assert_eq!(function_access["width_bytes"], 4);
        assert_eq!(function_access["region"], "Stack");
        assert_eq!(function_access["base_object"], "SP");
        assert_eq!(function_access["provenance"], "stack-relative address rooted at SP");
        assert_eq!(function_access["origin"]["instruction_address"], 0x1000);
        assert_eq!(function_access["origin"]["instruction_size"], 4);
        assert_eq!(function_access["origin"]["encoding"], encoding);
        assert_eq!(
            function_access["origin"]["instruction_bytes"],
            serde_json::json!(encoding.to_le_bytes().to_vec())
        );
        assert_eq!(json["memory_model"]["accesses"][0]["origin"], function_access["origin"]);
        assert!(json["unsupported"]["records"].as_array().is_some_and(Vec::is_empty));
    }

    #[test]
    fn test_aarch64_lift_narrow_load_store_facts_preserve_exact_instruction_provenance() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x39400020, 0x1000), // LDRB W0, [X1]
                decode_aarch64(0x79000820, 0x1004), // STRH W0, [X1, #4]
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (_blocks, _layout, facts) = lift_cfg_semantic_with_facts(&cfg, LiftArch::Aarch64)
            .expect("AArch64 narrow load/store fixture should lift");

        let read = facts
            .iter()
            .find(|fact| fact.kind == MemoryAccessKind::Read && fact.width_bytes == 1)
            .expect("LDRB should emit a byte read fact");
        assert_eq!(read.origin.function_entry, Some(0x1000));
        assert_eq!(read.origin.instruction_address, 0x1000);
        assert_eq!(read.origin.instruction_size, Some(4));
        assert_eq!(read.origin.encoding, Some(0x39400020));
        assert_eq!(read.origin.instruction_bytes, 0x39400020u32.to_le_bytes().to_vec());

        let write = facts
            .iter()
            .find(|fact| fact.kind == MemoryAccessKind::Write && fact.width_bytes == 2)
            .expect("STRH should emit a halfword write fact");
        assert_eq!(write.origin.function_entry, Some(0x1000));
        assert_eq!(write.origin.instruction_address, 0x1004);
        assert_eq!(write.origin.instruction_size, Some(4));
        assert_eq!(write.origin.encoding, Some(0x79000820));
        assert_eq!(write.origin.instruction_bytes, 0x79000820u32.to_le_bytes().to_vec());
    }

    #[test]
    fn test_aarch64_lift_pair_load_store_fixture_records_each_memory_access() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xA9400440, 0x1000), // LDP X0, X1, [X2]
                decode_aarch64(0xA9BF7BFD, 0x1004), // STP X29, X30, [SP, #-16]!
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, facts) = lift_cfg_semantic_with_facts(&cfg, LiftArch::Aarch64)
            .expect("AArch64 pair load/store fixture should lift");

        assert_eq!(blocks.len(), 1);
        assert!(has_assign_to(&blocks[0], layout.gpr(0)), "LDP should write X0");
        assert!(has_assign_to(&blocks[0], layout.gpr(1)), "LDP should write X1");
        assert_eq!(
            facts
                .iter()
                .filter(|fact| { fact.kind == MemoryAccessKind::Read && fact.width_bytes == 8 })
                .count(),
            2,
            "LDP should emit one read fact per destination register"
        );
        assert_eq!(
            facts
                .iter()
                .filter(|fact| { fact.kind == MemoryAccessKind::Write && fact.width_bytes == 8 })
                .count(),
            2,
            "STP should emit one write fact per source register"
        );
        assert!(facts.iter().any(|fact| {
            fact.kind == MemoryAccessKind::Write
                && fact.region == MemoryRegionKind::Stack
                && fact.offset == Some(Formula::BitVec { value: -16, width: 64 })
        }));
        assert!(facts.iter().any(|fact| {
            fact.kind == MemoryAccessKind::Write
                && fact.region == MemoryRegionKind::Stack
                && fact.offset == Some(Formula::BitVec { value: -8, width: 64 })
        }));
        assert!(
            has_assign_to(&blocks[0], layout.sp_local),
            "pre-indexed STP should make SP writeback proof-visible"
        );
    }

    #[test]
    fn test_aarch64_lift_frame_record_prologue_epilogue_preserves_sp_and_provenance() {
        let stp = 0xA9BF7BFD; // STP X29, X30, [SP, #-16]!
        let mov_fp = 0x910003FD; // ADD X29, SP, #0
        let ldp = 0xA8C17BFD; // LDP X29, X30, [SP], #16
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(stp, 0x1000),
                decode_aarch64(mov_fp, 0x1004),
                decode_aarch64(ldp, 0x1008),
                decode_aarch64(0xD65F03C0, 0x100C), // RET
            ],
            true,
        );

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("AArch64 frame-record prologue/epilogue should lift exactly");

        assert!(unsupported.is_empty(), "exact frame-record lift should not use the ledger");
        assert_eq!(facts.len(), 4, "STP/LDP frame record should emit two facts each");
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(
            has_assign_to_with(&blocks[0], layout.gpr(29), |rvalue| {
                matches!(rvalue, Rvalue::Use(Operand::Symbolic(Formula::BvAdd(_, _, 64))))
            }),
            "ADD X29, SP, #0 should make the frame-pointer materialization proof-visible"
        );
        assert!(
            blocks[0].stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(base, offset, 64))),
                        span,
                    } if place.local == layout.sp_local
                        && span.binary_address_value() == Some(0x1000)
                        && stack_relative_offset(base) == Some(0)
                        && matches!(
                            offset.as_ref(),
                            Formula::BitVec { value: -16, width: 64 }
                        )
                )
            }),
            "pre-indexed STP should write SP - 16 at the STP instruction"
        );
        assert!(
            blocks[0].stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    Statement::Assign {
                        place,
                        rvalue: Rvalue::Use(Operand::Symbolic(Formula::BvAdd(base, offset, 64))),
                        span,
                    } if place.local == layout.sp_local
                        && span.binary_address_value() == Some(0x1008)
                        && stack_relative_offset(base) == Some(-16)
                        && matches!(
                            offset.as_ref(),
                            Formula::BitVec { value: 16, width: 64 }
                        )
                )
            }),
            "post-indexed LDP should write back SP + 16 at the LDP instruction"
        );

        for (kind, insn_addr, encoding, offset) in [
            (MemoryAccessKind::Write, 0x1000, stp, -16),
            (MemoryAccessKind::Write, 0x1000, stp, -8),
            (MemoryAccessKind::Read, 0x1008, ldp, -16),
            (MemoryAccessKind::Read, 0x1008, ldp, -8),
        ] {
            let fact = facts
                .iter()
                .find(|fact| {
                    fact.kind == kind
                        && fact.origin.instruction_address == insn_addr
                        && fact.offset == Some(Formula::BitVec { value: offset, width: 64 })
                })
                .expect("frame-record memory fact should retain exact stack offset");
            assert_eq!(fact.width_bytes, 8);
            assert_eq!(fact.region, MemoryRegionKind::Stack);
            assert_eq!(fact.base_object.as_deref(), Some("SP"));
            assert_eq!(fact.provenance.as_deref(), Some("stack-relative address rooted at SP"));
            assert_eq!(fact.origin.function_entry, Some(0x1000));
            assert_eq!(fact.origin.instruction_size, Some(4));
            assert_eq!(fact.origin.encoding, Some(encoding));
            assert_eq!(fact.origin.instruction_bytes, encoding.to_le_bytes().to_vec());
        }
    }

    #[test]
    fn test_aarch64_lift_w_pair_load_store_preserves_widths_pc_and_provenance() {
        let ldp = 0x294113E3; // LDP W3, W4, [SP, #8]
        let stp = 0x29021BE5; // STP W5, W6, [SP, #16]
        let ldp_insn = decode_aarch64(ldp, 0x1000);
        let stp_insn = decode_aarch64(stp, 0x1004);
        assert_eq!(ldp_insn.opcode, Opcode::Ldp);
        assert_eq!(stp_insn.opcode, Opcode::Stp);

        let cfg =
            cfg_with_block(vec![ldp_insn, stp_insn, decode_aarch64(0xD65F03C0, 0x1008)], true);

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("32-bit AArch64 pair load/store forms should lift exactly");

        assert!(unsupported.is_empty(), "exact W-pair lift should not use the ledger");
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(has_assign_to(&blocks[0], layout.gpr(3)), "LDP W3 should write X3 local");
        assert!(has_assign_to(&blocks[0], layout.gpr(4)), "LDP W4 should write X4 local");
        assert_eq!(assign_count_to(&blocks[0], layout.mem_local), 2);
        assert!(has_pc_assign_to(&blocks[0], layout.pc_local, 0x1000, 0x1004));
        assert!(has_pc_assign_to(&blocks[0], layout.pc_local, 0x1004, 0x1008));

        assert_eq!(facts.len(), 4, "LDP/STP W-pair should emit one fact per element");
        for (kind, insn_addr, encoding, offset) in [
            (MemoryAccessKind::Read, 0x1000, ldp, 8),
            (MemoryAccessKind::Read, 0x1000, ldp, 12),
            (MemoryAccessKind::Write, 0x1004, stp, 16),
            (MemoryAccessKind::Write, 0x1004, stp, 20),
        ] {
            let fact = facts
                .iter()
                .find(|fact| {
                    fact.kind == kind
                        && fact.origin.instruction_address == insn_addr
                        && fact.offset == Some(Formula::BitVec { value: offset, width: 64 })
                })
                .expect("W-pair memory fact should retain exact stack offset");
            assert_eq!(fact.width_bytes, 4);
            assert_eq!(fact.region, MemoryRegionKind::Stack);
            assert_eq!(fact.base_object.as_deref(), Some("SP"));
            assert_eq!(fact.provenance.as_deref(), Some("stack-relative address rooted at SP"));
            assert_eq!(fact.origin.function_entry, Some(0x1000));
            assert_eq!(fact.origin.instruction_size, Some(4));
            assert_eq!(fact.origin.encoding, Some(encoding));
            assert_eq!(fact.origin.instruction_bytes, encoding.to_le_bytes().to_vec());
        }
    }

    #[test]
    fn test_aarch64_lift_malformed_pair_load_fails_closed_with_provenance() {
        let encoding = 0x29400440; // LDP W0, W1, [X2] with operands intentionally unavailable.
        let cfg = cfg_with_block(
            vec![
                aarch64_fallthrough_opcode(encoding, 0x1000, Opcode::Ldp),
                decode_aarch64(0xD65F03C0, 0x1004),
            ],
            true,
        );

        let err = lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
            .expect_err("malformed pair load should fail closed");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("opcode Ldp")
                && message.contains("invalid operand at index 0")
                && message.contains("expected GPR pair register")
        ));

        let rendered = err.to_string();
        assert!(rendered.contains("binary:0x1000 size 4 encoding 0x29400440"));
        assert!(rendered.contains("bytes [0x40, 0x04, 0x40, 0x29]"));
    }

    #[test]
    fn test_aarch64_lift_indexed_load_store_fixture_makes_writeback_visible() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xF8410C20, 0x1000), // LDR X0, [X1, #16]!
                decode_aarch64(0xF81F8420, 0x1004), // STR X0, [X1], #-8
                decode_aarch64(0xD65F03C0, 0x1008), // RET
            ],
            true,
        );

        let (blocks, layout, facts) = lift_cfg_semantic_with_facts(&cfg, LiftArch::Aarch64)
            .expect("AArch64 indexed load/store fixture should lift");

        assert_eq!(blocks.len(), 1);
        assert!(
            assign_count_to(&blocks[0], layout.gpr(1)) >= 2,
            "pre- and post-indexed forms should both assign the base register"
        );
        assert!(
            facts
                .iter()
                .any(|fact| { fact.kind == MemoryAccessKind::Read && fact.width_bytes == 8 })
        );
        assert!(
            facts
                .iter()
                .any(|fact| { fact.kind == MemoryAccessKind::Write && fact.width_bytes == 8 })
        );
    }

    #[test]
    fn test_aarch64_lift_ldr_literal_text_region_fails_closed_with_typed_blocker() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x58000080, 0x1000), // LDR X0, #0x1010
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic_with_region_hints(
            &cfg,
            LiftArch::Aarch64,
            MemoryRegionHints::text(0x1000, 0x100),
        )
        .expect_err("literal pool loads require proof-consumed literal bytes and replay witnesses");

        let rendered = err.to_string();
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 literal load semantics are unsupported fail-closed")
                && message.contains("opcode LdrLiteral")
                && message.contains("literal load to X0 (64-bit)")
                && message.contains("PC-relative literal offset 16")
        ));
        assert!(rendered.contains("binary:0x1000 size 4 encoding 0x58000080"), "{rendered}");
        assert!(rendered.contains("typed proof blocker"), "{rendered}");
        assert!(rendered.contains("unsupported-ledger coverage"), "{rendered}");
        assert!(rendered.contains("proof-consumed literal-load witnesses"), "{rendered}");
        assert!(rendered.contains("status=not proof-consumed"), "{rendered}");
    }

    #[test]
    fn test_aarch64_lift_ldr_literal_pc_relative_region_fails_closed_without_memory_fact() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x58000080, 0x1000), // LDR X0, #0x1010
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic_with_region_hints(
            &cfg,
            LiftArch::Aarch64,
            MemoryRegionHints::text(0x2000, 0x100),
        )
        .expect_err("literal pool loads should fail before region classification");

        let rendered = err.to_string();
        assert!(rendered.contains("AArch64 literal load semantics are unsupported fail-closed"));
        assert!(rendered.contains("literal load to X0 (64-bit)"), "{rendered}");
        assert!(rendered.contains("PC-relative literal offset 16"), "{rendered}");
        assert!(
            !rendered.contains("unclassified AArch64 literal load region"),
            "literal loads should fail at the proof boundary, before memory-region ledger fallback: {rendered}"
        );
    }

    #[test]
    fn test_aarch64_lift_ldr_literal_operand_edge_fails_closed_with_typed_blocker() {
        let cfg = cfg_with_block(
            vec![
                aarch64_fallthrough_opcode(0x58000080, 0x1000, Opcode::LdrLiteral),
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("literal-load operand decode edges must fail closed");
        let rendered = err.to_string();
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 literal load semantics are unsupported fail-closed")
                && message.contains("opcode LdrLiteral")
                && message.contains("expected scalar destination register for literal load")
        ));
        assert!(rendered.contains("binary:0x1000 size 4 encoding 0x58000080"), "{rendered}");
        assert!(rendered.contains("bytes [0x80, 0x00, 0x00, 0x58]"), "{rendered}");
        assert!(rendered.contains("typed proof blocker"), "{rendered}");
        assert!(rendered.contains("unsupported-ledger coverage"), "{rendered}");
        assert!(rendered.contains("proof-consumed literal-load witnesses"), "{rendered}");
        assert!(rendered.contains("status=not proof-consumed"), "{rendered}");
    }

    #[test]
    fn test_aarch64_lift_internal_direct_branch_fixture() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x14000002, 0x1000)], // B #0x8 -> 0x1008
            successors: vec![0x1008],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1008,
            instructions: vec![decode_aarch64(0xD65F03C0, 0x1008)], // RET
            successors: vec![],
            is_return: true,
        });

        let (blocks, _) = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect("internal direct branch should lift to a Goto");

        assert_eq!(blocks.len(), 2);
        assert!(matches!(blocks[0].terminator, Terminator::Goto(BlockId(1))));
        assert!(matches!(blocks[1].terminator, Terminator::Return));
    }

    #[test]
    fn test_aarch64_lift_cbz_cbnz_exact_pc_update_cfg_and_empty_ledger() {
        for (encoding, expected_negated) in [
            (0xB4000080, false), // CBZ X0, #0x10
            (0xB5000080, true),  // CBNZ X0, #0x10
        ] {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.encoding, encoding);
            assert_eq!(insn.bytes, encoding.to_le_bytes().to_vec());
            assert_eq!(insn.branch_target(), Some(0x1010));

            let mut cfg = Cfg::new();
            cfg.add_block(LiftedBlock {
                id: 0,
                start_addr: 0x1000,
                instructions: vec![insn],
                successors: vec![0x1004, 0x1010],
                is_return: false,
            });
            cfg.add_block(LiftedBlock {
                id: 1,
                start_addr: 0x1004,
                instructions: vec![],
                successors: vec![],
                is_return: true,
            });
            cfg.add_block(LiftedBlock {
                id: 2,
                start_addr: 0x1010,
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
                CfgEdgeTarget::Internal(0x1010),
            )));

            let (blocks, layout, facts, unsupported) =
                lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                    .expect("CBZ/CBNZ should lift exactly");
            assert!(facts.is_empty());
            assert!(unsupported.is_empty());

            let pc_formula = pc_assign_formula(&blocks[0], layout.pc_local);
            match pc_formula {
                Formula::Ite(cond, target, fallthrough) => {
                    assert_zero_compare_condition(cond, "X0", 64, expected_negated);
                    assert_eq!(constant_pc_value(target), Some(0x1010));
                    assert_eq!(constant_pc_value(fallthrough), Some(0x1004));
                }
                other => panic!("expected CBZ/CBNZ PC ITE, got {other:?}"),
            }

            match &blocks[0].terminator {
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    assert_zero_compare_condition(
                        symbolic_formula(discr),
                        "X0",
                        64,
                        expected_negated,
                    );
                    assert_eq!(targets, &vec![(1, BlockId(2))]);
                    assert_eq!(*otherwise, BlockId(1));
                }
                other => panic!("expected SwitchInt, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_lift_cbz_derives_switch_from_pc_update_ite() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0xB4000080, 0x1000)], // CBZ X0, #0x10
            successors: vec![0x1004, 0x1010],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, _) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("CBZ should lift through PC ITE");
        match &blocks[0].terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                assert!(matches!(discr, Operand::Symbolic(Formula::Eq(_, _))));
                assert_eq!(targets, &vec![(1, BlockId(2))]);
                assert_eq!(*otherwise, BlockId(1));
            }
            other => panic!("expected SwitchInt, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_bcond_derives_switch_from_nzcv_flag() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x54000100, 0x1000)], // B.EQ #0x20 -> 0x1020
            successors: vec![0x1004, 0x1020],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, _) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("B.cond should lift through NZCV");
        match &blocks[0].terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                assert!(matches!(symbolic_formula(discr), Formula::Var(name, _) if name == "_Z"));
                assert_eq!(targets, &vec![(1, BlockId(2))]);
                assert_eq!(*otherwise, BlockId(1));
            }
            other => panic!("expected SwitchInt, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_bcond_emits_exact_pc_update_ite() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x54000100, 0x1000)], // B.EQ #0x20 -> 0x1020
            successors: vec![0x1004, 0x1020],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("B.cond PC update should lift exactly");

        assert!(unsupported.is_empty());
        let pc_formula = blocks[0]
            .stmts
            .iter()
            .find_map(|stmt| match stmt {
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Symbolic(formula)),
                    ..
                } if place.local == layout.pc_local => Some(formula),
                _ => None,
            })
            .expect("B.cond should materialize a symbolic PC update");

        match pc_formula {
            Formula::Ite(cond, target, fallthrough) => {
                assert!(matches!(cond.as_ref(), Formula::Var(name, _) if name == "_Z"));
                assert_eq!(constant_pc_value(target), Some(0x1020));
                assert_eq!(constant_pc_value(fallthrough), Some(0x1004));
            }
            other => panic!("expected PC ITE for B.cond, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_ccmp_b_eq_uses_exact_conditional_flags_without_ledger() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![
                decode_aarch64(0xFA45082A, 0x1000), // CCMP X1, #5, #0b1010, EQ
                decode_aarch64(0x54000080, 0x1004), // B.EQ #0x10 -> 0x1014
            ],
            successors: vec![0x1008, 0x1014],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1008,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1014,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("CCMP feeding B.EQ should lift as exact scalar flag semantics");

        assert!(unsupported.is_empty());
        assert!(facts.is_empty());
        assert!(has_assign_to(&blocks[0], layout.flag_z));
        assert!(
            !has_assign_to(&blocks[0], layout.gpr(1)),
            "CCMP should compare X1 without writing a GPR destination"
        );

        match &blocks[0].terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let formula = symbolic_formula(discr);
                assert!(
                    matches!(formula, Formula::Ite(..)),
                    "CCMP should make B.EQ depend on conditional NZCV selection"
                );
                assert!(
                    formula_contains_bv_sub(formula),
                    "CCMP taken arm should preserve the exact subtraction comparison"
                );
                assert_eq!(targets, &vec![(1, BlockId(2))]);
                assert_eq!(*otherwise, BlockId(1));
            }
            other => panic!("expected SwitchInt, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_cbnz_derives_switch_from_pc_update_ite() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0xB5000080, 0x1000)], // CBNZ X0, #0x10
            successors: vec![0x1004, 0x1010],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, _) =
            lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("CBNZ should lift through PC ITE");
        match &blocks[0].terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                assert!(matches!(discr, Operand::Symbolic(Formula::Not(_))));
                assert_eq!(targets, &vec![(1, BlockId(2))]);
                assert_eq!(*otherwise, BlockId(1));
            }
            other => panic!("expected SwitchInt, got {other:?}"),
        }
    }

    #[test]
    fn test_aarch64_lift_tbz_tbnz_derives_switch_from_bit_extract() {
        for (encoding, target_addr, expected_negated) in [
            (0x36280080, 0x1010, false), // TBZ X0, #5, #0x10
            (0x37180040, 0x1008, true),  // TBNZ W0, #3, #0x8
        ] {
            let mut cfg = Cfg::new();
            cfg.add_block(LiftedBlock {
                id: 0,
                start_addr: 0x1000,
                instructions: vec![decode_aarch64(encoding, 0x1000)],
                successors: vec![0x1004, target_addr],
                is_return: false,
            });
            cfg.add_block(LiftedBlock {
                id: 1,
                start_addr: 0x1004,
                instructions: vec![],
                successors: vec![],
                is_return: true,
            });
            cfg.add_block(LiftedBlock {
                id: 2,
                start_addr: target_addr,
                instructions: vec![],
                successors: vec![],
                is_return: true,
            });

            let (blocks, _) =
                lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect("TBZ/TBNZ should lift");
            match &blocks[0].terminator {
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    let formula = symbolic_formula(discr);
                    assert_eq!(matches!(formula, Formula::Not(_)), expected_negated);
                    assert!(
                        formula_contains_bv_extract(formula),
                        "TBZ/TBNZ condition should test a concrete bit"
                    );
                    assert_eq!(targets, &vec![(1, BlockId(2))]);
                    assert_eq!(*otherwise, BlockId(1));
                }
                other => panic!("expected SwitchInt, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_aarch64_lift_tbz_tbnz_exact_bit_test_cfg_and_empty_ledger() {
        for (encoding, target_addr, bit, expected_negated) in [
            (0x36280080, 0x1010, 5, false), // TBZ X0, #5, #0x10
            (0x37180040, 0x1008, 3, true),  // TBNZ W0, #3, #0x8
        ] {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.encoding, encoding);
            assert_eq!(insn.bytes, encoding.to_le_bytes().to_vec());
            assert_eq!(insn.branch_target(), Some(target_addr));

            let mut cfg = Cfg::new();
            cfg.add_block(LiftedBlock {
                id: 0,
                start_addr: 0x1000,
                instructions: vec![insn],
                successors: vec![0x1004, target_addr],
                is_return: false,
            });
            cfg.add_block(LiftedBlock {
                id: 1,
                start_addr: 0x1004,
                instructions: vec![],
                successors: vec![],
                is_return: true,
            });
            cfg.add_block(LiftedBlock {
                id: 2,
                start_addr: target_addr,
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
                CfgEdgeTarget::Internal(target_addr),
            )));

            let (blocks, layout, facts, unsupported) =
                lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                    .expect("TBZ/TBNZ should lift exactly");
            assert!(facts.is_empty());
            assert!(unsupported.is_empty());

            let pc_formula = pc_assign_formula(&blocks[0], layout.pc_local);
            match pc_formula {
                Formula::Ite(cond, target, fallthrough) => {
                    assert_bit_test_condition(cond, "X0", bit, expected_negated);
                    assert_eq!(constant_pc_value(target), Some(target_addr));
                    assert_eq!(constant_pc_value(fallthrough), Some(0x1004));
                }
                other => panic!("expected TBZ/TBNZ PC ITE, got {other:?}"),
            }

            match &blocks[0].terminator {
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    assert_bit_test_condition(symbolic_formula(discr), "X0", bit, expected_negated);
                    assert_eq!(targets, &vec![(1, BlockId(2))]);
                    assert_eq!(*otherwise, BlockId(1));
                }
                other => panic!("expected SwitchInt, got {other:?}"),
            }
        }
    }

    #[test]
    fn test_aarch64_lift_branch_test_target_mismatch_fails_closed() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![decode_aarch64(0x36280080, 0x1000)], // TBZ X0, #5, #0x10
            successors: vec![0x1004, 0x1020],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.add_block(LiftedBlock {
            id: 3,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let err = lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
            .expect_err("mismatched branch-test CFG target should fail closed");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("final PC ITE destinations do not match recovered CFG")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: semantic lift proof mode: block 0 at 0x1000 final PC ITE destinations do not match recovered CFG: target 0x1010 vs 0x1020, fallthrough 0x1004 vs 0x1004"
        );
    }

    #[test]
    fn test_aarch64_unsupported_semantics_error_preserves_instruction_provenance() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD53B4200, 0x1000), // MRS X0, NZCV
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect_err("MRS is unsupported");
        let message = err.to_string();
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("unsupported instruction semantics")
        ));
        assert!(message.contains("unsupported instruction semantics"));
        assert!(message.contains("binary:0x1000 size 4 encoding 0xd53b4200"));
        assert!(message.contains("bytes [0x00, 0x42, 0x3b, 0xd5]"));
        assert!(message.contains("Mrs"));
        assert!(
            message
                .contains("MRS reads system register NZCV (S3_3_C4_C2_0, encoded 0xda10) into X0"),
            "MRS diagnostic should include exact system register and destination: {message}"
        );
        assert!(message.contains("typed proof blocker"), "{message}");
        assert!(message.contains("unsupported-ledger coverage"), "{message}");
        assert!(message.contains("proof-consumed system-register witnesses"), "{message}");
        assert!(message.contains("status=not proof-consumed"), "{message}");
    }

    #[test]
    fn test_aarch64_lift_system_register_write_fails_closed() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD51B4200, 0x1000), // MSR NZCV, X0
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("MSR must fail closed until system register state is modeled");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 system register semantics are unsupported fail-closed")
                && message.contains("opcode Msr")
        ));
        let rendered = err.to_string();
        assert!(rendered.contains("binary:0x1000 size 4 encoding 0xd51b4200"));
        assert!(rendered.contains("bytes [0x00, 0x42, 0x1b, 0xd5]"));
        assert!(
            rendered
                .contains("MSR writes system register NZCV (S3_3_C4_C2_0, encoded 0xda10) from X0"),
            "MSR diagnostic should include exact system register and source: {rendered}"
        );
        assert!(rendered.contains("typed proof blocker"), "{rendered}");
        assert!(rendered.contains("unsupported-ledger coverage"), "{rendered}");
        assert!(rendered.contains("proof-consumed system-register witnesses"), "{rendered}");
        assert!(rendered.contains("status=not proof-consumed"), "{rendered}");
    }

    #[test]
    fn test_aarch64_binary_cfg_system_register_boundary_fails_closed_with_diagnostics() {
        let cases: &[(u32, Opcode, &str, &str)] = &[
            (
                0xD53B_4200,
                Opcode::Mrs,
                "MRS X0, NZCV",
                "MRS reads system register NZCV (S3_3_C4_C2_0, encoded 0xda10) into X0",
            ),
            (
                0xD51B_4200,
                Opcode::Msr,
                "MSR NZCV, X0",
                "MSR writes system register NZCV (S3_3_C4_C2_0, encoded 0xda10) from X0",
            ),
        ];
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();

        for &(encoding, opcode, mnemonic, expected_detail) in cases {
            let mut code = Vec::new();
            code.extend_from_slice(&encoding.to_le_bytes());
            code.extend_from_slice(&0xD65F_03C0u32.to_le_bytes()); // RET

            let cfg = crate::cfg_builder::recover_cfg(
                &decoder,
                LiftArch::Aarch64,
                &code,
                0x1000,
                0x1000,
                0x1008,
            )
            .expect("system-register access should recover as fallthrough CFG bytes");
            assert_eq!(cfg.block_count(), 1, "{mnemonic} should stay in the entry block");

            let block = &cfg.blocks[0];
            assert_eq!(block.instructions.len(), 2, "{mnemonic} plus RET should decode");
            assert_eq!(block.instructions[0].opcode, opcode, "{mnemonic} decoded opcode");
            assert_eq!(block.instructions[0].encoding, encoding);
            assert_eq!(block.instructions[0].bytes, encoding.to_le_bytes());

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("system-register access requires privileged-state proof semantics");
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains("AArch64 system register semantics are unsupported fail-closed")
                    && message.contains(&format!("opcode {opcode:?}"))
                    && message.contains(expected_detail)
            ));

            let rendered = err.to_string();
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic} diagnostic should include exact binary provenance: {rendered}"
            );
            assert!(
                rendered.contains("bytes ["),
                "{mnemonic} diagnostic should include raw instruction bytes: {rendered}"
            );
            assert!(
                rendered.contains("outside the scalar model"),
                "{mnemonic} diagnostic should explain the privileged-state boundary: {rendered}"
            );
            assert!(
                rendered.contains("typed proof blocker"),
                "{mnemonic} diagnostic should name the proof blocker: {rendered}"
            );
            assert!(
                rendered.contains("unsupported-ledger coverage"),
                "{mnemonic} diagnostic should name the ledger boundary: {rendered}"
            );
            assert!(
                rendered.contains("proof-consumed system-register witnesses"),
                "{mnemonic} diagnostic should name required proof consumption: {rendered}"
            );
            assert!(
                rendered.contains("status=not proof-consumed"),
                "{mnemonic} diagnostic should carry proof-consumption status: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_lift_system_barrier_records_partial_boundary_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD5033B9F, 0x1000), // DMB ISH
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, _layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("barriers should lift as partial semantic boundaries");
        assert_eq!(unsupported.records.len(), 1);
        assert!(
            !blocks[0].stmts.is_empty(),
            "DMB should not erase the lifted instruction stream; PC advance remains explicit"
        );
        let record = &unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::semantic-lift");
        assert_eq!(record.architecture.as_deref(), Some("aarch64"));
        assert_eq!(record.opcode.as_deref(), Some("Dmb"));
        assert_eq!(record.operand.as_deref(), Some("ISH full"));
        assert!(record.feature.contains("AArch64 synchronization boundary"));
        assert!(record.feature.contains("kind=DataMemoryBarrier"));
        assert!(record.feature.contains("scope=InnerShareable"));
        assert!(record.feature.contains("ordering=LoadsAndStores"));
        assert!(record.feature.contains("raw_option=0xb"));
        assert!(record.feature.contains("not proof-grade"));
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.encoding), Some(0xD5033B9F));
    }

    #[test]
    fn test_aarch64_lift_isb_records_partial_boundary_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD5033FDF, 0x1000), // ISB
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("ISB should lift as a partial instruction-synchronization boundary");
        assert_eq!(unsupported.records.len(), 1);
        let record = &unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::semantic-lift");
        assert_eq!(record.architecture.as_deref(), Some("aarch64"));
        assert_eq!(record.opcode.as_deref(), Some("Isb"));
        assert_eq!(record.operand.as_deref(), Some("SY full"));
        assert!(record.feature.contains("kind=InstructionSynchronizationBarrier"));
        assert!(record.feature.contains("ordering=InstructionStream"));
        assert!(record.feature.contains("not proof-grade"));
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.encoding), Some(0xD5033FDF));
    }

    #[test]
    fn test_aarch64_lift_clrex_records_monitor_clear_boundary_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD503305F, 0x1000), // CLREX #0
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("CLREX should lift as an explicit monitor-clear boundary");
        assert_eq!(unsupported.records.len(), 1);
        let record = &unsupported.records[0];
        assert_eq!(record.stage, "trust-lift::semantic-lift");
        assert_eq!(record.architecture.as_deref(), Some("aarch64"));
        assert_eq!(record.opcode.as_deref(), Some("Clrex"));
        assert_eq!(record.operand.as_deref(), None);
        assert!(record.feature.contains("kind=ClearExclusiveMonitor"));
        assert!(record.feature.contains("scope=Local"));
        assert!(record.feature.contains("ordering=None"));
        assert!(record.feature.contains("clears_exclusive_monitor=true"));
        assert!(record.feature.contains("raw_option=0x0"));
        assert!(record.feature.contains("not proof-grade"));
    }

    #[test]
    fn test_aarch64_barrier_and_clrex_ledger_records_name_proof_blocker_provenance() {
        let cases = [
            (
                0xD5033B9F,
                "Dmb",
                Some("ISH full"),
                "DataMemoryBarrier",
                "InnerShareable",
                "LoadsAndStores",
                false,
                "0xb",
            ),
            (
                0xD5033F3F,
                "Dsb",
                Some("SY full"),
                "DataSynchronizationBarrier",
                "FullSystem",
                "LoadsAndStores",
                false,
                "0xf",
            ),
            (
                0xD5033FDF,
                "Isb",
                Some("SY full"),
                "InstructionSynchronizationBarrier",
                "FullSystem",
                "InstructionStream",
                false,
                "0xf",
            ),
            (0xD503305F, "Clrex", None, "ClearExclusiveMonitor", "Local", "None", true, "0x0"),
        ];

        for (encoding, opcode, operand, kind, scope, ordering, clears_monitor, raw_option) in cases
        {
            let cfg = cfg_with_block(
                vec![
                    decode_aarch64(encoding, 0x1000),
                    decode_aarch64(0xD65F03C0, 0x1004), // RET
                ],
                true,
            );

            let (_blocks, _layout, _facts, unsupported) =
                lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                    .expect("AArch64 barriers should lift as explicit partial ledger records");
            assert_eq!(unsupported.records.len(), 1, "{opcode}");
            let record = &unsupported.records[0];
            assert_eq!(record.stage, "trust-lift::semantic-lift", "{opcode}");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"), "{opcode}");
            assert_eq!(record.opcode.as_deref(), Some(opcode), "{opcode}");
            assert_eq!(record.operand.as_deref(), operand, "{opcode}");
            assert!(
                record.feature.contains("AArch64 synchronization boundary"),
                "{opcode}: {}",
                record.feature
            );
            assert!(record.feature.contains("unsupported-ledger boundary"), "{opcode}");
            assert!(record.feature.contains(&format!("kind={kind}")), "{opcode}");
            assert!(record.feature.contains(&format!("scope={scope}")), "{opcode}");
            assert!(record.feature.contains(&format!("ordering={ordering}")), "{opcode}");
            assert!(
                record.feature.contains(&format!("clears_exclusive_monitor={clears_monitor}")),
                "{opcode}"
            );
            assert!(record.feature.contains(&format!("raw_option={raw_option}")), "{opcode}");
            assert!(record.feature.contains("not proof-grade"), "{opcode}");
            assert!(record.feature.contains("proof-consumed"), "{opcode}");

            let origin = record.origin.as_ref().expect("ledger record must carry binary origin");
            assert_eq!(origin.function_entry, Some(0x1000), "{opcode}");
            assert_eq!(origin.instruction_address, 0x1000, "{opcode}");
            assert_eq!(origin.instruction_size, Some(4), "{opcode}");
            assert_eq!(origin.encoding, Some(encoding), "{opcode}");
            assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec(), "{opcode}");
            assert!(origin.source.is_none(), "{opcode}");
        }
    }

    #[test]
    fn test_aarch64_lift_prfm_is_supported_without_ledger_or_memory_fact() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xF9800020, 0x1000), // PRFM #0, [X1]
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("PRFM should lift as supported no-data prefetch semantics");
        assert!(unsupported.is_empty());
        assert!(facts.is_empty(), "PRFM should not be modeled as a memory read or write");
    }

    #[test]
    fn test_aarch64_lift_yield_hint_is_supported_without_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD503203F, 0x1000), // YIELD
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("YIELD should lift as supported scalar no-data semantics");
        assert!(unsupported.is_empty());
    }

    #[test]
    fn test_aarch64_lift_supported_boundaries_plus_barriers_records_only_barrier_boundaries() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD503203F, 0x1000), // YIELD
                decode_aarch64(0xD5033FDF, 0x1004), // ISB
                decode_aarch64(0xD503305F, 0x1008), // CLREX #0
                decode_aarch64(0xD5033B9F, 0x100C), // DMB ISH
                decode_aarch64(0xD65F03C0, 0x1010), // RET
            ],
            true,
        );

        let (_blocks, _layout, _facts, unsupported) = lift_cfg_semantic_with_facts_and_ledger(
            &cfg,
            LiftArch::Aarch64,
        )
        .expect(
            "supported no-data system instructions should not add ledger records next to barriers",
        );
        assert_eq!(unsupported.records.len(), 3);
        let isb_record = &unsupported.records[0];
        assert_eq!(isb_record.opcode.as_deref(), Some("Isb"));
        assert_eq!(isb_record.operand.as_deref(), Some("SY full"));
        assert!(isb_record.feature.contains("InstructionSynchronizationBarrier"));
        assert_eq!(
            isb_record.origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x1004)
        );
        let clrex_record = &unsupported.records[1];
        assert_eq!(clrex_record.opcode.as_deref(), Some("Clrex"));
        assert!(clrex_record.feature.contains("ClearExclusiveMonitor"));
        assert!(clrex_record.feature.contains("clears_exclusive_monitor=true"));
        let dmb_record = &unsupported.records[2];
        assert_eq!(dmb_record.opcode.as_deref(), Some("Dmb"));
        assert_eq!(dmb_record.operand.as_deref(), Some("ISH full"));
        assert!(dmb_record.feature.contains("DataMemoryBarrier"));
        assert_eq!(
            dmb_record.origin.as_ref().map(|origin| origin.instruction_address),
            Some(0x100C)
        );
        assert_eq!(dmb_record.origin.as_ref().and_then(|origin| origin.encoding), Some(0xD5033B9F));
        assert_eq!(
            dmb_record.origin.as_ref().map(|origin| origin.instruction_bytes.as_slice()),
            Some(&[0x9F, 0x3B, 0x03, 0xD5][..])
        );
    }

    #[test]
    fn test_aarch64_lift_wait_hints_fail_closed_with_typed_proof_blockers() {
        let cases = [
            (
                0xD503205F,
                Opcode::Wfe,
                "WFE",
                "event register state",
                "wakeup/invalidation conditions",
            ),
            (0xD503207F, Opcode::Wfi, "WFI", "interrupt mask/state", "wakeup conditions"),
        ];

        for (encoding, opcode, mnemonic, state_detail, wake_detail) in cases {
            let cfg = cfg_with_block(
                vec![
                    decode_aarch64(encoding, 0x1000),
                    decode_aarch64(0xD65F03C0, 0x1004), // RET
                ],
                true,
            );

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("wait hints require explicit system wait proof semantics");
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains("AArch64 system wait/hint semantics are unsupported fail-closed")
                    && message.contains(&format!("opcode {opcode:?}"))
                    && message.contains("typed proof blocker")
                    && message.contains(state_detail)
                    && message.contains(wake_detail)
            ));

            let rendered = err.to_string();
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic} diagnostic should include exact instruction provenance: {rendered}"
            );
            assert!(
                rendered.contains("unsupported-ledger coverage"),
                "{mnemonic} diagnostic should name the proof ledger boundary: {rendered}"
            );
            assert!(
                rendered.contains("drop the wait/synchronization boundary"),
                "{mnemonic} diagnostic should explain why no-op lowering is blocked: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_lift_dsb_remains_partial_boundary_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD5033F3F, 0x1000), // DSB SY
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (_blocks, _layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("DSB should remain an explicit partial semantic boundary");
        assert_eq!(unsupported.records.len(), 1);
        let record = &unsupported.records[0];
        assert_eq!(record.opcode.as_deref(), Some("Dsb"));
        assert_eq!(record.operand.as_deref(), Some("SY full"));
        assert!(record.feature.contains("DataSynchronizationBarrier"));
        assert!(record.feature.contains("scope=FullSystem"));
        assert!(record.feature.contains("not proof-grade"));
    }

    #[test]
    fn test_aarch64_lift_unsupported_syscall_is_documented() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD4000001, 0x1000), // SVC #0
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("syscalls should fail closed in proof-grade lifting");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 syscall/trap semantics are unsupported fail-closed")
        ));
        assert!(err.to_string().contains("binary:0x1000 size 4 encoding 0xd4000001"));
        assert!(err.to_string().contains("bytes [0x01, 0x00, 0x00, 0xd4]"));
        assert!(err.to_string().contains("typed proof blocker"));
        assert!(err.to_string().contains("unsupported-ledger coverage"));
        assert!(err.to_string().contains("proof-consumed syscall/trap witnesses"));
        assert!(err.to_string().contains("status=not proof-consumed"));
    }

    #[test]
    fn test_aarch64_lift_exception_trap_family_fails_closed_with_immediates() {
        let cases = [
            (
                0xD4000041,
                Opcode::Svc,
                2,
                "AArch64 syscall/trap",
                "SVC exception immediate #2",
                "kernel",
            ),
            (
                0xD4000062,
                Opcode::Hvc,
                3,
                "AArch64 privileged trap",
                "HVC exception immediate #3",
                "hypervisor",
            ),
            (
                0xD4000083,
                Opcode::Smc,
                4,
                "AArch64 privileged trap",
                "SMC exception immediate #4",
                "secure monitor",
            ),
            (
                0xD42000A0,
                Opcode::Brk,
                5,
                "AArch64 trap",
                "BRK exception immediate #5",
                "debug exception",
            ),
            (
                0xD44000C0,
                Opcode::Hlt,
                6,
                "AArch64 trap",
                "HLT exception immediate #6",
                "halt/debug exception",
            ),
        ];

        for (encoding, opcode, imm, category, immediate_detail, boundary_detail) in cases {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.opcode, opcode);
            assert!(matches!(insn.operand(0), Some(DisasmOperand::Imm(actual)) if *actual == imm));
            let cfg = cfg_with_block(vec![insn, decode_aarch64(0xD65F03C0, 0x1004)], true);

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("exception/trap instructions must fail closed");
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains(&format!(
                    "{category} semantics are unsupported fail-closed"
                )) && message.contains(&format!("opcode {opcode:?}"))
                    && message.contains(immediate_detail)
                    && message.contains(boundary_detail)
            ));
            let rendered = err.to_string();
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{opcode:?} diagnostic should include exact instruction provenance: {rendered}"
            );
            assert!(
                rendered.contains("bytes ["),
                "{opcode:?} diagnostic should include raw instruction bytes: {rendered}"
            );
            assert!(
                rendered.contains("typed proof blocker"),
                "{opcode:?} diagnostic should name the proof blocker: {rendered}"
            );
            assert!(
                rendered.contains("unsupported-ledger coverage"),
                "{opcode:?} diagnostic should name the unsupported ledger boundary: {rendered}"
            );
            assert!(
                rendered.contains("proof-consumed syscall/trap witnesses"),
                "{opcode:?} diagnostic should name the required proof witnesses: {rendered}"
            );
            assert!(
                rendered.contains("status=not proof-consumed"),
                "{opcode:?} diagnostic should carry proof-consumption status: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_lift_ldar_stlr_fail_closed_as_ordering_boundaries() {
        type OrderingBoundaryCase = (
            u32,
            &'static str,
            &'static str,
            &'static str,
            &'static str,
            MemoryAccessKind,
            trust_types::MemoryOrderingSemantics,
            &'static [&'static str],
        );

        let cases: &[OrderingBoundaryCase] = &[
            (
                0xC8DFFC20,
                "LDAR X0, [X1]",
                "Ldar",
                "Load",
                "Acquire",
                MemoryAccessKind::Read,
                trust_types::MemoryOrderingSemantics::Acquire,
                &[
                    "acquire ordering event",
                    "synchronization edge",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            (
                0xC89FFC20,
                "STLR X0, [X1]",
                "Stlr",
                "Store",
                "Release",
                MemoryAccessKind::Write,
                trust_types::MemoryOrderingSemantics::Release,
                &[
                    "release ordering event",
                    "synchronization edge",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
        ];

        for &(
            encoding,
            mnemonic,
            opcode_name,
            access_kind,
            ordering,
            memory_kind,
            fact_ordering,
            expected_witnesses,
        ) in cases
        {
            let cfg = cfg_with_block(
                vec![
                    decode_aarch64(encoding, 0x1000),
                    decode_aarch64(0xD65F03C0, 0x1004), // RET
                ],
                true,
            );

            let err = lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect_err("acquire/release ordered memory instructions need proof witnesses");
            let rendered = err.to_string();
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains(
                    "AArch64 atomic memory-order semantics are unsupported fail-closed"
                ) && message.contains(&format!("opcode {opcode_name}"))
            ));
            assert!(rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")));
            assert!(rendered.contains("unsupported-ledger coverage"), "{mnemonic}: {rendered}");
            assert!(rendered.contains(&format!("access={access_kind}")), "{mnemonic}");
            assert!(rendered.contains(&format!("ordering={ordering}")), "{mnemonic}");
            assert!(rendered.contains("exclusive_monitor=None"), "{mnemonic}: {rendered}");
            assert!(rendered.contains("reports_status=false"), "{mnemonic}: {rendered}");
            assert!(rendered.contains("proof-consumed witnesses are required"), "{mnemonic}");
            for witness in expected_witnesses {
                assert!(rendered.contains(witness), "{mnemonic}: {rendered}");
            }

            let insn = decode_aarch64(encoding, 0x1000);
            let (category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("LDAR/STLR blocker category");
            assert_eq!(category, "AArch64 atomic memory-order");

            let record = unsupported_aarch64_semantics_record(
                Some(0x1000),
                LiftArch::Aarch64,
                &insn,
                category,
                &detail,
            );
            assert_eq!(record.stage, "trust-lift::semantic-lift");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"));
            assert_eq!(record.opcode.as_deref(), Some(opcode_name));
            assert!(record.operand.as_deref().is_some_and(|operand| !operand.is_empty()));
            assert!(record.feature.contains("AArch64 atomic memory-order"));
            assert!(record.feature.contains("unsupported fail-closed"));
            assert!(record.feature.contains(&format!("access={access_kind}")));
            assert!(record.feature.contains(&format!("ordering={ordering}")));
            assert!(record.feature.contains("exclusive_monitor=None"));
            assert!(record.feature.contains("synchronization edge"));
            assert!(record.feature.contains("happens-before witness"));
            assert!(record.feature.contains("status=not proof-consumed"));
            assert_eq!(record.family_tag(), "binary.aarch64.memory_order_boundary");
            let origin = record.origin.as_ref().expect("LDAR/STLR ledger origin");
            assert_eq!(origin.function_entry, Some(0x1000), "{mnemonic}");
            assert_eq!(origin.instruction_address, 0x1000, "{mnemonic}");
            assert_eq!(origin.instruction_size, Some(4), "{mnemonic}");
            assert_eq!(origin.encoding, Some(encoding), "{mnemonic}");
            assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec(), "{mnemonic}");

            let fact = record
                .aarch64_atomic_semantic_fact()
                .expect("LDAR/STLR fail-closed boundary should expose typed ordering fact");
            assert_eq!(fact.opcode, opcode_name, "{mnemonic}");
            assert!(fact.operand.as_deref().is_some_and(|operand| !operand.is_empty()));
            assert_eq!(fact.access, memory_kind, "{mnemonic}");
            assert_eq!(fact.ordering, fact_ordering, "{mnemonic}");
            assert_eq!(
                fact.exclusive_monitor,
                trust_types::Aarch64ExclusiveMonitorSemantics::None,
                "{mnemonic}"
            );
            assert!(!fact.reports_status, "{mnemonic}");
            let actual_witnesses =
                fact.missing_witnesses.iter().map(String::as_str).collect::<Vec<_>>();
            assert_eq!(actual_witnesses.as_slice(), expected_witnesses, "{mnemonic}");
            assert!(!fact.consumed_by_proof_model, "{mnemonic}");
            assert!(!fact.proof_grade_gate_accepted(), "{mnemonic}");
            let rejection = fact
                .proof_grade_rejection_reason()
                .expect("LDAR/STLR facts should remain proof blockers");
            assert!(rejection.contains("not proof-consumed"), "{mnemonic}: {rejection}");
            for witness in expected_witnesses {
                assert!(rejection.contains(witness), "{mnemonic}: {rejection}");
            }
        }
    }

    #[test]
    fn test_aarch64_lift_exclusive_memory_order_fails_closed() {
        let cases = [
            (0xC85F7C20, "LDXR X0, [X1]", "Ldxr", "Load", "Relaxed", "LoadReserve", false),
            (0xC8027C20, "STXR W2, X0, [X1]", "Stxr", "Store", "Relaxed", "StoreConditional", true),
            (0xC85FFC20, "LDAXR X0, [X1]", "Ldaxr", "Load", "Acquire", "LoadReserve", false),
            (
                0xC802FC20,
                "STLXR W2, X0, [X1]",
                "Stlxr",
                "Store",
                "Release",
                "StoreConditional",
                true,
            ),
        ];

        for (
            encoding,
            mnemonic,
            opcode_name,
            access,
            ordering,
            monitor_operation,
            reports_status,
        ) in cases
        {
            let cfg = cfg_with_block(
                vec![
                    decode_aarch64(encoding, 0x1000),
                    decode_aarch64(0xD65F03C0, 0x1004), // RET
                ],
                true,
            );

            let err = match lift_cfg_semantic(&cfg, LiftArch::Aarch64) {
                Ok(_) => panic!("{mnemonic} should fail closed in proof-grade lifting"),
                Err(err) => err,
            };
            let message = err.to_string();
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains(
                    "AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed"
                )
            ));
            assert!(message.contains("unsupported-ledger coverage"), "{mnemonic}: {message}");
            assert!(message.contains(opcode_name), "{mnemonic}: {message}");
            assert_aarch64_exclusive_blocker_detail(
                &message,
                access,
                ordering,
                monitor_operation,
                reports_status,
            );
            assert!(
                message.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic}: {message}"
            );
            assert!(message.contains(&format!(
                "bytes [0x{:02x}, 0x{:02x}, 0x{:02x}, 0x{:02x}]",
                encoding & 0xff,
                (encoding >> 8) & 0xff,
                (encoding >> 16) & 0xff,
                (encoding >> 24) & 0xff
            )));
        }
    }

    #[test]
    fn test_aarch64_exclusive_unsupported_ledger_record_preserves_opcode_bytes_and_family() {
        let cases = [
            (
                0xC85F7C20,
                Opcode::Ldxr,
                "LDXR",
                "Load",
                "Relaxed",
                "LoadReserve",
                trust_types::MemoryAccessKind::Read,
                trust_types::MemoryOrderingSemantics::Relaxed,
                trust_types::Aarch64ExclusiveMonitorSemantics::LoadReserve,
                false,
            ),
            (
                0xC8027C20,
                Opcode::Stxr,
                "STXR",
                "Store",
                "Relaxed",
                "StoreConditional",
                trust_types::MemoryAccessKind::Write,
                trust_types::MemoryOrderingSemantics::Relaxed,
                trust_types::Aarch64ExclusiveMonitorSemantics::StoreConditional,
                true,
            ),
            (
                0xC85FFC20,
                Opcode::Ldaxr,
                "LDAXR",
                "Load",
                "Acquire",
                "LoadReserve",
                trust_types::MemoryAccessKind::Read,
                trust_types::MemoryOrderingSemantics::Acquire,
                trust_types::Aarch64ExclusiveMonitorSemantics::LoadReserve,
                false,
            ),
            (
                0xC802FC20,
                Opcode::Stlxr,
                "STLXR",
                "Store",
                "Release",
                "StoreConditional",
                trust_types::MemoryAccessKind::Write,
                trust_types::MemoryOrderingSemantics::Release,
                trust_types::Aarch64ExclusiveMonitorSemantics::StoreConditional,
                true,
            ),
        ];

        for (
            encoding,
            opcode,
            mnemonic,
            access,
            ordering,
            monitor_operation,
            expected_access,
            expected_ordering,
            expected_monitor,
            expected_reports_status,
        ) in cases
        {
            let insn = decode_aarch64(encoding, 0x401008);
            assert_eq!(insn.opcode, opcode, "{mnemonic} decoder fixture");
            let (category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("atomic semantic gap");

            let record = unsupported_aarch64_semantics_record(
                Some(0x401000),
                LiftArch::Aarch64,
                &insn,
                category,
                &detail,
            );

            assert_eq!(record.stage, "trust-lift::semantic-lift");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"));
            let expected_opcode = format!("{opcode:?}");
            assert_eq!(record.opcode.as_deref(), Some(expected_opcode.as_str()));
            assert!(record.operand.as_deref().is_some_and(|operand| !operand.is_empty()));
            assert!(record.feature.contains("unsupported fail-closed"), "{mnemonic}");
            assert_aarch64_exclusive_blocker_detail(
                &record.feature,
                access,
                ordering,
                monitor_operation,
                expected_reports_status,
            );
            assert_eq!(record.family_tag(), "binary.aarch64.memory_order_boundary");

            let fact = record
                .aarch64_atomic_semantic_fact()
                .expect("atomic fail-closed record should expose a typed semantic fact");
            assert_eq!(
                fact.origin.as_ref().map(|origin| origin.instruction_address),
                Some(0x401008)
            );
            assert_eq!(fact.access, expected_access, "{mnemonic}");
            assert_eq!(fact.ordering, expected_ordering, "{mnemonic}");
            assert_eq!(fact.exclusive_monitor, expected_monitor, "{mnemonic}");
            assert_eq!(fact.reports_status, expected_reports_status, "{mnemonic}");
            assert!(
                !fact.proof_grade_gate_accepted(),
                "{mnemonic} typed fact must not satisfy proof-grade acceptance by itself"
            );
            assert!(
                fact.proof_grade_rejection_reason()
                    .is_some_and(|reason| reason.contains("missing witnesses")),
                "{mnemonic} typed fact should explain residual proof witnesses"
            );

            let origin = record.origin.as_ref().expect("binary origin");
            assert_eq!(origin.function_entry, Some(0x401000));
            assert_eq!(origin.instruction_address, 0x401008);
            assert_eq!(origin.instruction_size, Some(4));
            assert_eq!(origin.encoding, Some(encoding));
            assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec());
        }
    }

    #[test]
    fn test_aarch64_exclusive_monitor_diagnostics_bind_witnesses_provenance_and_gate() {
        use trust_types::{
            Aarch64ExclusiveMonitorSemantics as Monitor, MemoryAccessKind as Access,
            MemoryOrderingSemantics as Ordering,
        };

        type ExclusiveMonitorCase =
            (u32, Opcode, &'static str, Access, Ordering, Monitor, bool, &'static [&'static str]);

        let cases: &[ExclusiveMonitorCase] = &[
            (
                0xC85F7C20,
                Opcode::Ldxr,
                "LDXR X0, [X1]",
                Access::Read,
                Ordering::Relaxed,
                Monitor::LoadReserve,
                false,
                &[
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                ],
            ),
            (
                0x885F7C20,
                Opcode::Ldxr,
                "LDXR W0, [X1]",
                Access::Read,
                Ordering::Relaxed,
                Monitor::LoadReserve,
                false,
                &[
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                ],
            ),
            (
                0xC8027C20,
                Opcode::Stxr,
                "STXR W2, X0, [X1]",
                Access::Write,
                Ordering::Relaxed,
                Monitor::StoreConditional,
                true,
                &[
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                ],
            ),
            (
                0x88027C20,
                Opcode::Stxr,
                "STXR W2, W0, [X1]",
                Access::Write,
                Ordering::Relaxed,
                Monitor::StoreConditional,
                true,
                &[
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                ],
            ),
            (
                0xC85FFC20,
                Opcode::Ldaxr,
                "LDAXR X0, [X1]",
                Access::Read,
                Ordering::Acquire,
                Monitor::LoadReserve,
                false,
                &[
                    "acquire ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            (
                0x885F_FC83,
                Opcode::Ldaxr,
                "LDAXR W3, [X4]",
                Access::Read,
                Ordering::Acquire,
                Monitor::LoadReserve,
                false,
                &[
                    "acquire ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            (
                0xC802FC20,
                Opcode::Stlxr,
                "STLXR W2, X0, [X1]",
                Access::Write,
                Ordering::Release,
                Monitor::StoreConditional,
                true,
                &[
                    "release ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
            (
                0x8805_FC83,
                Opcode::Stlxr,
                "STLXR W5, W3, [X4]",
                Access::Write,
                Ordering::Release,
                Monitor::StoreConditional,
                true,
                &[
                    "release ordering event",
                    "synchronization edge",
                    "exclusive-monitor reservation state",
                    "exclusive-monitor invalidation",
                    "store-conditional status result",
                    "thread identity",
                    "happens-before witness",
                ],
            ),
        ];

        for &(
            encoding,
            opcode,
            mnemonic,
            expected_access,
            expected_ordering,
            expected_monitor,
            expected_reports_status,
            expected_witnesses,
        ) in cases
        {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.opcode, opcode, "{mnemonic} decoder fixture");
            let expected_opcode = format!("{opcode:?}");
            let expected_bytes = encoding.to_le_bytes().to_vec();

            let cfg = cfg_with_block(vec![insn.clone(), decode_aarch64(0xD65F03C0, 0x1004)], true);
            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("exclusive monitor instructions must fail closed");
            let rendered = err.to_string();
            assert!(rendered.contains(&format!("opcode {expected_opcode}")), "{mnemonic}");
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic}: {rendered}"
            );
            assert!(
                rendered.contains(&format!("bytes {}", instruction_bytes_display(&expected_bytes))),
                "{mnemonic}: {rendered}"
            );
            assert!(rendered.contains("monitor reservation state"), "{mnemonic}: {rendered}");
            assert!(rendered.contains("monitor invalidation"), "{mnemonic}: {rendered}");
            assert!(
                rendered.contains("proof-consumed witnesses are required"),
                "{mnemonic}: {rendered}"
            );
            assert!(rendered.contains("unsupported-ledger coverage"), "{mnemonic}: {rendered}");
            if expected_reports_status {
                assert!(
                    rendered.contains("store-conditional status result"),
                    "{mnemonic}: {rendered}"
                );
            }

            let (category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("exclusive monitor blocker");
            let record = unsupported_aarch64_semantics_record(
                Some(0x1000),
                LiftArch::Aarch64,
                &insn,
                category,
                &detail,
            );
            assert_eq!(record.opcode.as_deref(), Some(expected_opcode.as_str()), "{mnemonic}");
            assert_eq!(record.family_tag(), "binary.aarch64.memory_order_boundary", "{mnemonic}");

            let origin = record.origin.as_ref().expect("exclusive ledger origin");
            assert_eq!(origin.function_entry, Some(0x1000), "{mnemonic}");
            assert_eq!(origin.instruction_address, 0x1000, "{mnemonic}");
            assert_eq!(origin.instruction_size, Some(4), "{mnemonic}");
            assert_eq!(origin.encoding, Some(encoding), "{mnemonic}");
            assert_eq!(origin.instruction_bytes, expected_bytes, "{mnemonic}");

            let fact = record
                .aarch64_atomic_semantic_fact()
                .expect("exclusive ledger record must expose a typed atomic fact");
            assert_eq!(fact.opcode, expected_opcode, "{mnemonic}");
            assert_eq!(fact.access, expected_access, "{mnemonic}");
            assert_eq!(fact.ordering, expected_ordering, "{mnemonic}");
            assert_eq!(fact.exclusive_monitor, expected_monitor, "{mnemonic}");
            assert_eq!(fact.reports_status, expected_reports_status, "{mnemonic}");
            assert_eq!(
                fact.missing_witnesses,
                expected_witnesses.iter().map(|witness| witness.to_string()).collect::<Vec<_>>(),
                "{mnemonic}"
            );
            assert!(!fact.consumed_by_proof_model, "{mnemonic}");
            assert!(!fact.proof_grade_gate_accepted(), "{mnemonic}");

            let rejection = fact
                .proof_grade_rejection_reason()
                .expect("exclusive monitor facts remain proof blockers");
            assert!(rejection.contains("not proof-consumed"), "{mnemonic}: {rejection}");
            for witness in expected_witnesses {
                assert!(rejection.contains(witness), "{mnemonic}: {rejection}");
            }
        }
    }

    #[test]
    fn test_aarch64_fail_closed_proof_boundaries_are_unsupported_ledger_visible() {
        let cases: &[(u32, Opcode, &str, &[&str])] = &[
            (
                0x5800_0080,
                Opcode::LdrLiteral,
                "AArch64 literal load",
                &[
                    "literal load to X0",
                    "PC-relative literal offset",
                    "proof-consumed literal-load witnesses",
                ],
            ),
            (
                0xC8DF_FC20,
                Opcode::Ldar,
                "AArch64 atomic memory-order",
                &[
                    "ordering=Acquire",
                    "exclusive_monitor=None",
                    "acquire ordering event",
                    "happens-before witness",
                ],
            ),
            (
                0xC89F_FC20,
                Opcode::Stlr,
                "AArch64 atomic memory-order",
                &[
                    "ordering=Release",
                    "exclusive_monitor=None",
                    "release ordering event",
                    "happens-before witness",
                ],
            ),
            (
                0xC85F_FC20,
                Opcode::Ldaxr,
                "AArch64 atomic/exclusive memory-order",
                &[
                    "ordering=Acquire",
                    "monitor_operation=LoadReserve",
                    "exclusive monitor semantics are fail-closed",
                    "happens-before witness",
                ],
            ),
            (
                0xD53B_4200,
                Opcode::Mrs,
                "AArch64 system register",
                &[
                    "MRS reads system register NZCV",
                    "system register bank",
                    "proof-consumed system-register witnesses",
                ],
            ),
            (
                0x1E62_2820,
                Opcode::Fadd,
                "AArch64 FP/SIMD",
                &[
                    "instruction_family=aarch64.fp_arithmetic",
                    "blocker_code=aarch64-fp-simd-compute-not-proof-consumed",
                    "proof-consumed FP/SIMD compute witnesses",
                ],
            ),
            (
                0xD400_0001,
                Opcode::Svc,
                "AArch64 syscall/trap",
                &[
                    "SVC exception immediate",
                    "can enter the kernel",
                    "proof-consumed syscall/trap witnesses",
                ],
            ),
            (
                0xD420_0020,
                Opcode::Brk,
                "AArch64 trap",
                &[
                    "BRK exception immediate",
                    "raises a debug exception",
                    "proof-consumed syscall/trap witnesses",
                ],
            ),
        ];

        for &(encoding, opcode, category, expected_terms) in cases {
            let insn = decode_aarch64(encoding, 0x401008);
            assert_eq!(insn.opcode, opcode, "{category}");

            let ledger = aarch64_fail_closed_proof_boundary_ledger(Some(0x401000), &insn);
            assert_eq!(ledger.records.len(), 1, "{category}");
            let record = &ledger.records[0];

            assert_eq!(record.stage, "trust-lift::semantic-lift", "{category}");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"), "{category}");
            let expected_opcode = format!("{opcode:?}");
            assert_eq!(record.opcode.as_deref(), Some(expected_opcode.as_str()), "{category}");
            assert!(
                record
                    .feature
                    .contains(&format!("{category} semantics are unsupported fail-closed")),
                "{category}: {}",
                record.feature
            );
            assert!(
                record.feature.contains("unsupported-ledger coverage"),
                "{category}: {}",
                record.feature
            );
            assert!(record.feature.contains("proof-consumed"), "{category}: {}", record.feature);
            for expected in expected_terms {
                assert!(
                    record.feature.contains(expected),
                    "{category}: missing {expected:?} in {}",
                    record.feature
                );
            }

            let origin = record.origin.as_ref().expect("fail-closed ledger origin");
            assert_eq!(origin.function_entry, Some(0x401000), "{category}");
            assert_eq!(origin.instruction_address, 0x401008, "{category}");
            assert_eq!(origin.instruction_size, Some(4), "{category}");
            assert_eq!(origin.encoding, Some(encoding), "{category}");
            assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec(), "{category}");

            let (actual_category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("fail-closed category");
            assert_eq!(actual_category, category);
            let err = unsupported_aarch64_instruction_semantics_error(
                Some(0x401000),
                &insn,
                actual_category,
                &detail,
            );
            let rendered = err.to_string();
            assert!(
                rendered.contains("unsupported-ledger coverage stage trust-lift::semantic-lift"),
                "{category}: {rendered}"
            );
            assert!(
                rendered.contains(&format!("binary:0x401008 size 4 encoding 0x{encoding:08x}")),
                "{category}: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_lift_unsupported_fp_simd_is_documented() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x1E622820, 0x1000), // FADD D0, D1, D2
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("FP writes are not representable in the current TrustIr layout");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 FP/SIMD semantics are unsupported fail-closed")
        ));
        assert!(err.to_string().contains("binary:0x1000 size 4 encoding 0x1e622820"));
    }

    #[test]
    fn test_aarch64_binary_cfg_fp_simd_fails_closed_with_proof_diagnostics() {
        let encoding = 0x1E62_2820u32; // FADD D0, D1, D2
        let mut code = Vec::new();
        code.extend_from_slice(&encoding.to_le_bytes());
        code.extend_from_slice(&0xD65F_03C0u32.to_le_bytes()); // RET

        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let cfg = crate::cfg_builder::recover_cfg(
            &decoder,
            LiftArch::Aarch64,
            &code,
            0x1000,
            0x1000,
            0x1008,
        )
        .expect("FP/SIMD fallthrough should recover as raw AArch64 CFG bytes");
        assert_eq!(cfg.block_count(), 1);

        let block = &cfg.blocks[0];
        assert_eq!(block.instructions.len(), 2);
        assert_eq!(block.instructions[0].opcode, Opcode::Fadd);
        assert_eq!(block.instructions[0].encoding, encoding);
        assert_eq!(block.instructions[0].bytes, encoding.to_le_bytes());

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("FP/SIMD instructions require an explicit proof model");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 FP/SIMD semantics are unsupported fail-closed")
                && message.contains("proof-grade lift requires unsupported-ledger coverage")
                && message.contains("opcode Fadd")
        ));

        let rendered = err.to_string();
        assert!(
            rendered.contains("binary:0x1000 size 4 encoding 0x1e622820"),
            "FP/SIMD diagnostic should include exact instruction provenance: {rendered}"
        );
        assert!(
            rendered.contains("bytes [0x20, 0x28, 0x62, 0x1e]"),
            "FP/SIMD diagnostic should include raw instruction bytes: {rendered}"
        );
    }

    #[test]
    fn test_aarch64_fp_simd_blocker_carries_ledger_proof_status_without_fallback() {
        let encoding = 0x1E62_2820u32; // FADD D0, D1, D2
        let insn = decode_aarch64(encoding, 0x1000);
        assert_eq!(insn.opcode, Opcode::Fadd);
        let cfg = cfg_with_block(
            vec![insn.clone(), decode_aarch64(0xD65F_03C0, 0x1004)], // RET
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("FP/SIMD instructions must fail before scalar TrustIr lowering");
        let message = match &err {
            LiftError::UnsupportedSemantics { mode: LiftProofMode::SemanticLift, message } => {
                message
            }
            other => panic!("expected semantic proof blocker, got {other:?}"),
        };

        assert!(message.contains("AArch64 FP/SIMD semantics are unsupported fail-closed"));
        assert!(message.contains("opcode Fadd"));
        assert!(message.contains("binary:0x1000 size 4 encoding 0x1e622820"));
        assert!(message.contains("bytes [0x20, 0x28, 0x62, 0x1e]"));
        assert!(message.contains("unsupported-ledger coverage stage trust-lift::semantic-lift"));
        assert!(message.contains("operation=Fadd"));
        assert!(message.contains("instruction_family=aarch64.fp_arithmetic"));
        assert!(message.contains("operands=D0, D1, D2"));
        assert!(message.contains("blocker_code=aarch64-fp-simd-compute-not-proof-consumed"));
        assert!(message.contains("proof-consumed FP/SIMD compute witnesses"));
        assert!(message.contains("status=not proof-consumed"));
        assert!(message.contains("rejecting instead of scalar or Undef lowering"));

        let rendered = err.to_string();
        assert!(
            !rendered.contains("unsupported FP register write effect"),
            "FP/SIMD blocker should fire before emitting an FP write effect: {rendered}"
        );
        assert!(
            !rendered.contains("no TrustIr FP local layout"),
            "FP/SIMD blocker should not rely on a layout fallback failure: {rendered}"
        );

        let (category, detail) =
            unsupported_aarch64_semantics_reason(&insn).expect("FP/SIMD blocker category");
        assert_eq!(category, "AArch64 FP/SIMD");
        assert!(detail.contains("operation=Fadd"));
        assert!(detail.contains("instruction_family=aarch64.fp_arithmetic"));
        assert!(detail.contains("operands=D0, D1, D2"));
        assert!(detail.contains("blocker_code=aarch64-fp-simd-compute-not-proof-consumed"));
        assert!(detail.contains("FPCR rounding mode"));
        assert!(detail.contains("IEEE-754 flags/exceptions"));
        assert!(detail.contains("status=not proof-consumed"));
        assert!(detail.contains("rejecting instead of scalar or Undef lowering"));

        let record = unsupported_aarch64_semantics_record(
            Some(0x1000),
            LiftArch::Aarch64,
            &insn,
            category,
            &detail,
        );
        assert_eq!(record.stage, "trust-lift::semantic-lift");
        assert_eq!(record.architecture.as_deref(), Some("aarch64"));
        assert_eq!(record.opcode.as_deref(), Some("Fadd"));
        assert!(record.feature.contains("AArch64 FP/SIMD semantics are unsupported fail-closed"));
        assert!(record.feature.contains("instruction_family=aarch64.fp_arithmetic"));
        assert!(record.feature.contains("blocker_code=aarch64-fp-simd-compute-not-proof-consumed"));
        assert!(record.feature.contains("status=not proof-consumed"));

        let origin = record.origin.as_ref().expect("FP/SIMD ledger origin");
        assert_eq!(origin.function_entry, Some(0x1000));
        assert_eq!(origin.instruction_address, 0x1000);
        assert_eq!(origin.instruction_size, Some(4));
        assert_eq!(origin.encoding, Some(encoding));
        assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec());

        let record_json = serde_json::to_value(&record).expect("serialize FP/SIMD ledger record");
        let expected_origin = serde_json::json!({
            "binary_path": null,
            "function_entry": 0x1000,
            "instruction_address": 0x1000,
            "instruction_size": 4,
            "encoding": encoding,
            "instruction_bytes": encoding.to_le_bytes().to_vec(),
            "source": null
        });
        assert_eq!(record_json["stage"], "trust-lift::semantic-lift");
        assert_eq!(record_json["architecture"], "aarch64");
        assert_eq!(record_json["opcode"], "Fadd");
        assert_eq!(record_json["origin"], expected_origin);
        assert!(
            record_json["feature"]
                .as_str()
                .expect("feature string")
                .contains("instruction_family=aarch64.fp_arithmetic")
        );
    }

    #[test]
    fn test_aarch64_fp_simd_compute_blocker_classifies_each_compute_subfamily() {
        let cases = [
            (
                decode_aarch64(0x1E62_2820, 0x1000), // FADD D0, D1, D2
                "Fadd",
                "aarch64.fp_arithmetic",
                "D0, D1, D2",
            ),
            (
                aarch64_fallthrough_opcode(0x1E20_0000, 0x1000, Opcode::Fcvtzs),
                "Fcvtzs",
                "aarch64.fp_integer_conversion",
                "unavailable",
            ),
            (
                aarch64_fallthrough_opcode(0x0E20_1C00, 0x1000, Opcode::SimdMov),
                "SimdMov",
                "aarch64.simd_move",
                "unavailable",
            ),
        ];

        for (insn, opcode, instruction_family, operands) in cases {
            let (category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("FP/SIMD compute blocker");
            assert_eq!(category, "AArch64 FP/SIMD", "{opcode}");
            assert!(detail.contains(&format!("operation={opcode}")), "{opcode}: {detail}");
            assert!(
                detail.contains(&format!("instruction_family={instruction_family}")),
                "{opcode}: {detail}"
            );
            assert!(detail.contains(&format!("operands={operands}")), "{opcode}: {detail}");
            assert!(
                detail.contains("blocker_code=aarch64-fp-simd-compute-not-proof-consumed"),
                "{opcode}: {detail}"
            );
            assert!(detail.contains("typed proof blocker"), "{opcode}: {detail}");
            assert!(detail.contains("status=not proof-consumed"), "{opcode}: {detail}");

            let record = unsupported_aarch64_semantics_record(
                Some(0x1000),
                LiftArch::Aarch64,
                &insn,
                category,
                &detail,
            );
            assert_eq!(record.stage, "trust-lift::semantic-lift", "{opcode}");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"), "{opcode}");
            assert_eq!(record.opcode.as_deref(), Some(opcode), "{opcode}");
            assert!(
                record.feature.contains(&format!("instruction_family={instruction_family}")),
                "{opcode}: {}",
                record.feature
            );
            assert!(
                record.feature.contains("blocker_code=aarch64-fp-simd-compute-not-proof-consumed"),
                "{opcode}: {}",
                record.feature
            );

            let origin = record.origin.as_ref().expect("FP/SIMD compute ledger origin");
            assert_eq!(origin.function_entry, Some(0x1000), "{opcode}");
            assert_eq!(origin.instruction_address, 0x1000, "{opcode}");
            assert_eq!(origin.instruction_size, Some(4), "{opcode}");
            assert_eq!(origin.encoding, Some(insn.encoding), "{opcode}");
            assert_eq!(origin.instruction_bytes, insn.encoding.to_le_bytes().to_vec(), "{opcode}");
        }
    }

    #[test]
    fn test_aarch64_lift_fp_simd_load_store_fails_closed_with_typed_memory_blocker() {
        let cases = [
            (0x3D_C0_00_00, Opcode::Ldr, "LDR Q0, [X0]", "Q0", 128u16),
            (0x3D_80_04_41, Opcode::Str, "STR Q1, [X2, #16]", "Q1", 128u16),
        ];

        for (encoding, opcode, mnemonic, simd_reg, width) in cases {
            let insn = decode_aarch64(encoding, 0x1000);
            assert_eq!(insn.opcode, opcode, "{mnemonic}");
            let cfg = cfg_with_block(
                vec![insn.clone(), decode_aarch64(0xD65F_03C0, 0x1004)], // RET
                true,
            );

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("FP/SIMD load-store must fail before scalar memory lowering");
            let rendered = err.to_string();
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains(
                    "AArch64 FP/SIMD load-store semantics are unsupported fail-closed"
                ) && message.contains(&format!("opcode {opcode:?}"))
            ));
            assert!(
                rendered.contains(&format!("FP/SIMD register {simd_reg} ({width} bits)")),
                "{mnemonic}: {rendered}"
            );
            assert!(rendered.contains("typed proof blocker"), "{mnemonic}: {rendered}");
            assert!(
                rendered.contains("proof-consumed FP/SIMD memory witnesses"),
                "{mnemonic}: {rendered}"
            );
            assert!(
                rendered.contains("unsupported-ledger coverage stage trust-lift::semantic-lift"),
                "{mnemonic}: {rendered}"
            );
            assert!(rendered.contains("status=not proof-consumed"), "{mnemonic}: {rendered}");
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic}: {rendered}"
            );
            assert!(
                rendered.contains(&format!(
                    "bytes {}",
                    instruction_bytes_display(&encoding.to_le_bytes())
                )),
                "{mnemonic}: {rendered}"
            );
            assert!(
                !rendered.contains("unsupported FP register write effect"),
                "FP/SIMD load-store blocker should not rely on FP write fallback: {rendered}"
            );
            assert!(
                !rendered.contains("no TrustIr FP local layout"),
                "FP/SIMD load-store blocker should fire before layout fallback: {rendered}"
            );

            let (category, detail) =
                unsupported_aarch64_semantics_reason(&insn).expect("FP/SIMD memory blocker");
            assert_eq!(category, "AArch64 FP/SIMD load-store");
            assert!(detail.contains("FP/SIMD memory witnesses"), "{mnemonic}: {detail}");
            assert!(detail.contains("status=not proof-consumed"), "{mnemonic}: {detail}");

            let record = unsupported_aarch64_semantics_record(
                Some(0x1000),
                LiftArch::Aarch64,
                &insn,
                category,
                &detail,
            );
            assert_eq!(record.stage, "trust-lift::semantic-lift");
            assert_eq!(record.architecture.as_deref(), Some("aarch64"));
            let opcode_name = format!("{opcode:?}");
            assert_eq!(record.opcode.as_deref(), Some(opcode_name.as_str()));
            assert!(record.operand.as_deref().is_some_and(|operand| {
                operand.contains("Simd") && operand.contains(&format!("width: {width}"))
            }));
            assert!(
                record
                    .feature
                    .contains("AArch64 FP/SIMD load-store semantics are unsupported fail-closed"),
                "{mnemonic}: {}",
                record.feature
            );
            assert!(record.feature.contains("status=not proof-consumed"));

            let origin = record.origin.as_ref().expect("FP/SIMD load-store ledger origin");
            assert_eq!(origin.function_entry, Some(0x1000));
            assert_eq!(origin.instruction_address, 0x1000);
            assert_eq!(origin.instruction_size, Some(4));
            assert_eq!(origin.encoding, Some(encoding));
            assert_eq!(origin.instruction_bytes, encoding.to_le_bytes().to_vec());
        }
    }

    #[test]
    fn test_aarch64_lift_exclusive_ops_fail_closed_with_diagnostics() {
        let cases = [
            (0xC85F7C20, Opcode::Ldxr, "LDXR", "Load", "Relaxed", "LoadReserve", false),
            (0xC8027C20, Opcode::Stxr, "STXR", "Store", "Relaxed", "StoreConditional", true),
            (0xC85FFC20, Opcode::Ldaxr, "LDAXR", "Load", "Acquire", "LoadReserve", false),
            (0xC802FC20, Opcode::Stlxr, "STLXR", "Store", "Release", "StoreConditional", true),
        ];

        for (encoding, opcode, mnemonic, access, ordering, monitor_operation, reports_status) in
            cases
        {
            let cfg = cfg_with_block(
                vec![
                    aarch64_fallthrough_opcode(encoding, 0x1000, opcode),
                    decode_aarch64(0xD65F03C0, 0x1004), // RET
                ],
                true,
            );

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("atomic/exclusive instructions need an explicit proof model");
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains("AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed")
                    && message.contains(&format!("opcode {opcode:?}"))
            ));
            let rendered = err.to_string();
            assert_aarch64_exclusive_blocker_detail(
                &rendered,
                access,
                ordering,
                monitor_operation,
                reports_status,
            );
            assert!(
                rendered.contains(&format!("encoding 0x{encoding:08x}")),
                "{mnemonic} diagnostic should include instruction encoding: {rendered}"
            );
            assert!(
                rendered.contains("bytes ["),
                "{mnemonic} diagnostic should include raw instruction bytes: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_binary_cfg_32bit_acquire_release_exclusive_fails_closed() {
        let cases: &[(u32, Opcode, &str, &str, &str, &str, bool)] = &[
            (0x885F_FC83, Opcode::Ldaxr, "LDAXR W3, [X4]", "Load", "Acquire", "LoadReserve", false),
            (
                0x8805_FC83,
                Opcode::Stlxr,
                "STLXR W5, W3, [X4]",
                "Store",
                "Release",
                "StoreConditional",
                true,
            ),
        ];
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();

        for &(encoding, opcode, mnemonic, access, ordering, monitor_operation, reports_status) in
            cases
        {
            let mut code = Vec::new();
            code.extend_from_slice(&encoding.to_le_bytes());
            code.extend_from_slice(&0xD65F_03C0u32.to_le_bytes()); // RET

            let cfg = crate::cfg_builder::recover_cfg(
                &decoder,
                LiftArch::Aarch64,
                &code,
                0x1000,
                0x1000,
                0x1008,
            )
            .expect("memory-order instructions should recover as fallthrough CFG bytes");
            assert_eq!(cfg.block_count(), 1, "{mnemonic} should stay in the entry block");

            let block = &cfg.blocks[0];
            assert_eq!(block.instructions.len(), 2, "{mnemonic} plus RET should decode");
            assert_eq!(block.instructions[0].opcode, opcode, "{mnemonic} decoded opcode");
            assert_eq!(block.instructions[0].encoding, encoding);

            let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
                .expect_err("32-bit acquire/release-exclusive instructions need a proof model");
            assert!(matches!(
                &err,
                LiftError::UnsupportedSemantics {
                    mode: LiftProofMode::SemanticLift,
                    message
                } if message.contains("AArch64 atomic/exclusive memory-order semantics are unsupported fail-closed")
                    && message.contains(&format!("opcode {opcode:?}"))
            ));

            let rendered = err.to_string();
            assert_aarch64_exclusive_blocker_detail(
                &rendered,
                access,
                ordering,
                monitor_operation,
                reports_status,
            );
            assert!(
                rendered.contains(&format!("binary:0x1000 size 4 encoding 0x{encoding:08x}")),
                "{mnemonic} diagnostic should include exact binary provenance: {rendered}"
            );
            assert!(
                rendered.contains("unsupported-ledger coverage"),
                "{mnemonic} diagnostic should name the unsupported-ledger boundary: {rendered}"
            );
        }
    }

    #[test]
    fn test_aarch64_lift_fp_compare_records_partial_flag_boundary_ledger() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0x1E612000, 0x1000), // FCMP D0, D1
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let (blocks, layout, _facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::Aarch64)
                .expect("FCMP should lift as a partial flag boundary");

        assert!(has_assign_to(&blocks[0], layout.flag_z));
        assert_eq!(unsupported.records.len(), 1);
        let record = &unsupported.records[0];
        assert_eq!(record.opcode.as_deref(), Some("Fcmp"));
        assert!(record.feature.contains("FP compare"));
        assert!(record.feature.contains("unsupported-ledger boundary"));
        assert!(record.feature.contains("status=not proof-consumed"));
        assert!(record.feature.contains("proof-consumed"));
        assert!(record.feature.contains("scalar flag TrustIr is emitted with this ledger record"));
        assert!(record.feature.contains("instead of silent scalar/Undef lowering"));
        assert_eq!(record.origin.as_ref().and_then(|origin| origin.encoding), Some(0x1E612000));
        assert_eq!(
            record.origin.as_ref().map(|origin| origin.instruction_bytes.clone()),
            Some(0x1E612000u32.to_le_bytes().to_vec())
        );

        for stmt in &blocks[0].stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            assert!(
                [layout.flag_n, layout.flag_z, layout.flag_c, layout.flag_v, layout.pc_local,]
                    .contains(&place.local),
                "FCMP partial lowering should only emit guarded flag/PC scalar statements: {stmt:?}"
            );
            assert!(
                !format!("{rvalue:?}").contains("Undef"),
                "FCMP partial lowering must not manufacture Undef values: {stmt:?}"
            );
        }
        assert!(!has_assign_to(&blocks[0], layout.gpr(0)));
        assert!(!has_assign_to(&blocks[0], layout.mem_local));
    }

    #[test]
    fn test_aarch64_lift_unsupported_trap_is_documented() {
        let cfg = cfg_with_block(
            vec![
                decode_aarch64(0xD4200020, 0x1000), // BRK #1
                decode_aarch64(0xD65F03C0, 0x1004), // RET
            ],
            true,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64).expect_err("BRK should fail closed");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("AArch64 trap semantics are unsupported fail-closed")
        ));
        assert!(err.to_string().contains("binary:0x1000 size 4 encoding 0xd4200020"));
    }

    #[test]
    fn test_aarch64_lift_call_without_summary_is_documented_unsupported() {
        let cfg = cfg_with_block(
            vec![decode_aarch64(0x94000002, 0x1000)], // BL #0x8
            false,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::Aarch64)
            .expect_err("calls need callee summaries before proof-grade lifting");
        assert!(matches!(
            &err,
            LiftError::UnsupportedEffect {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("unsupported call effect")
        ));
    }

    #[test]
    fn test_x86_64_selected_no_data_slice_has_empty_unsupported_ledger() {
        let nop = decode_x86_64(&[0x90], 0x1000);
        let boundary = x86_64_empty_unsupported_ledger_boundary(&nop)
            .expect("NOP must be inside the exact x86_64 empty-ledger boundary");
        assert!(boundary.contains("exact-empty-ledger-boundary:x86_64.nop"));

        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![nop],
            successors: vec![0x1001],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1001,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let (blocks, layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::X86_64)
                .expect("selected x86_64 no-data slice should lift");

        assert_eq!(blocks.len(), 2);
        assert!(matches!(blocks[0].terminator, Terminator::Goto(BlockId(1))));
        assert!(matches!(blocks[1].terminator, Terminator::Return));
        assert!(facts.is_empty(), "NOP selected slice must not synthesize memory facts");
        assert!(
            unsupported.is_empty(),
            "selected x86_64 no-data slice is the only empty-ledger release boundary"
        );
        assert!(
            has_pc_assign_to(&blocks[0], layout.pc_local, 0x1000, 0x1001),
            "NOP should keep exact PC-advance provenance"
        );
    }

    #[test]
    fn test_x86_64_empty_unsupported_ledger_boundary_excludes_blockers() {
        let excluded = [
            (&[0xC3][..], Opcode::Ret, "ABI return target and stack witnesses"),
            (&[0x0F, 0x05][..], Opcode::Syscall, "kernel ABI side effects"),
            (&[0xCC][..], Opcode::Int3, "trap/exception boundary"),
            (&[0xE8, 0, 0, 0, 0][..], Opcode::Call, "callee summary and call ABI"),
            (&[0x48, 0x89, 0xE5][..], Opcode::Mov, "scalar dataflow outside no-data slice"),
        ];

        for (bytes, opcode, reason) in excluded {
            let insn = decode_x86_64(bytes, 0x1000);
            assert_eq!(insn.opcode, opcode, "{reason}");
            assert!(
                x86_64_empty_unsupported_ledger_boundary(&insn).is_none(),
                "{reason} must remain outside the exact empty-ledger boundary"
            );
        }
    }

    #[test]
    fn test_x86_64_ret_records_abi_unsupported_ledger_boundary() {
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0xC3], 0x1000)], // RET
            true,
        );

        let (_blocks, _layout, facts, unsupported) =
            lift_cfg_semantic_with_facts_and_ledger(&cfg, LiftArch::X86_64)
                .expect("x86_64 RET remains liftable but not release-claimed proof-grade");

        assert_eq!(facts.len(), 1, "RET should expose its stack return-target read");
        assert_eq!(unsupported.records.len(), 1);
        let record = &unsupported.records[0];
        assert_eq!(record.architecture.as_deref(), Some("x86_64"));
        assert_eq!(record.opcode.as_deref(), Some("Ret"));
        assert!(
            record.feature.contains("x86_64 ABI return boundary")
                && record.feature.contains("security/ABI VCs remain blockers"),
            "{record:?}"
        );
    }

    #[test]
    fn test_x86_64_syscall_unsupported_semantics_fails_closed_with_ledger_coverage() {
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x0F, 0x05], 0x1000)], // SYSCALL
            false,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::X86_64)
            .expect_err("SYSCALL requires proof-consumed kernel ABI witnesses");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("x86_64 syscall boundary semantics are unsupported fail-closed")
                && message.contains("kernel entry ABI")
                && message.contains("unsupported-ledger coverage")
                && message.contains("opcode Some(\"Syscall\")")
        ));
    }

    #[test]
    fn test_x86_64_call_unsupported_abi_boundary_fails_closed() {
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0xE8, 0, 0, 0, 0], 0x1000)], // CALL +0
            false,
        );

        let err = lift_cfg_semantic(&cfg, LiftArch::X86_64)
            .expect_err("CALL requires callee summaries before proof lifting");
        assert!(matches!(
            &err,
            LiftError::UnsupportedSemantics {
                mode: LiftProofMode::SemanticLift,
                message
            } if message.contains("x86_64 call ABI boundary semantics are unsupported fail-closed")
                && message.contains("callee summary")
                && message.contains("return-address stack write")
                && message.contains("unsupported-ledger coverage")
        ));
    }

    /// Trust: #573 — x86_64 RET-only function lifts to a single Return block.
    #[test]
    fn test_x86_64_lift_ret_only() {
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0xC3], 0x1000)], // RET
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 RET");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24); // x86_64 layout
        assert!(
            matches!(blocks[0].terminator, Terminator::Return),
            "RET block should have Return terminator"
        );
    }

    /// Trust: #573 — x86_64 MOV produces a register write in TrustIr.
    #[test]
    fn test_x86_64_lift_mov_reg_reg() {
        // 48 89 E5 = MOV RBP, RSP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x89, 0xE5], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 MOV");
        assert_eq!(blocks.len(), 1);

        // MOV RBP, RSP should produce an Assign to RBP (index 5 => local gpr(5)).
        let rbp_local = layout.gpr(5);
        let has_rbp_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rbp_local));
        assert!(has_rbp_assign, "MOV RBP, RSP should write RBP local");
    }

    /// Trust: #573 — x86_64 ADD produces register write and flag updates.
    #[test]
    fn test_x86_64_lift_add_sets_flags() {
        // 48 01 D0 = ADD RAX, RDX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x01, 0xD0], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 ADD");
        assert_eq!(blocks.len(), 1);

        // ADD RAX, RDX writes RAX (index 0 => local gpr(0)).
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(has_rax_assign, "ADD RAX, RDX should write RAX local");

        // ADD also sets EFLAGS (CF, ZF, SF, OF).
        let has_cf_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == layout.flag_n));
        assert!(has_cf_assign, "ADD should set flag locals");
    }

    /// Trust: #573 — x86_64 SUB RSP produces SP write.
    #[test]
    fn test_x86_64_lift_sub_rsp() {
        // 48 83 EC 20 = SUB RSP, 0x20
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x83, 0xEC, 0x20], 0x1000), decode_x86_64(&[0xC3], 0x1004)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 SUB RSP");
        assert_eq!(blocks.len(), 1);

        // SUB RSP, 0x20 should write the SP local.
        let has_sp_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.sp_local),
        );
        assert!(has_sp_assign, "SUB RSP, 0x20 should write SP local");
    }

    /// Trust: #573 — x86_64 CMP produces flags but no register write.
    #[test]
    fn test_x86_64_lift_cmp_no_writeback() {
        // 48 39 C8 = CMP RAX, RCX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x48, 0x39, 0xC8], 0x1000), decode_x86_64(&[0xC3], 0x1003)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 CMP");
        assert_eq!(blocks.len(), 1);

        // CMP should NOT write RAX.
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(!has_rax_assign, "CMP should not write RAX");

        // CMP should set flags.
        let has_flag_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == layout.flag_z));
        assert!(has_flag_assign, "CMP should set ZF flag");
    }

    /// Trust: #573 — x86_64 XOR EAX, EAX (zero idiom) lifts correctly.
    #[test]
    fn test_x86_64_lift_xor_zero_idiom() {
        // 31 C0 = XOR EAX, EAX
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x31, 0xC0], 0x1000), decode_x86_64(&[0xC3], 0x1002)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 XOR");
        assert_eq!(blocks.len(), 1);

        // XOR EAX, EAX should write EAX (32-bit RegWrite maps to RAX local).
        let rax_local = layout.gpr(0);
        let has_rax_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rax_local));
        assert!(has_rax_assign, "XOR EAX, EAX should write RAX local");
    }

    /// Trust: #573 — x86_64 PUSH/POP produces SP + MEM writes in TrustIr.
    #[test]
    fn test_x86_64_lift_push_pop() {
        // 55 = PUSH RBP
        // 5D = POP RBP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![
                decode_x86_64(&[0x55], 0x1000),
                decode_x86_64(&[0x5D], 0x1001),
                decode_x86_64(&[0xC3], 0x1002),
            ],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 PUSH/POP");
        assert_eq!(blocks.len(), 1);

        // PUSH writes SP and MEM; POP writes SP and RBP.
        let has_sp_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.sp_local),
        );
        let has_mem_assign = blocks[0].stmts.iter().any(
            |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.mem_local),
        );
        let rbp_local = layout.gpr(5);
        let has_rbp_assign = blocks[0]
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == rbp_local));
        assert!(has_sp_assign, "PUSH/POP should write SP local");
        assert!(has_mem_assign, "PUSH should write MEM local");
        assert!(has_rbp_assign, "POP should write RBP local");
    }

    /// Trust: #573 — x86_64 typical function prologue lifts end-to-end.
    ///
    /// Tests a realistic sequence: PUSH RBP; MOV RBP, RSP; SUB RSP, 0x20; ... ADD RSP, 0x20; POP RBP; RET
    #[test]
    fn test_x86_64_lift_function_prologue_epilogue() {
        let cfg = cfg_with_block(
            vec![
                decode_x86_64(&[0x55], 0x1000),                   // PUSH RBP
                decode_x86_64(&[0x48, 0x89, 0xE5], 0x1001),       // MOV RBP, RSP
                decode_x86_64(&[0x48, 0x83, 0xEC, 0x20], 0x1004), // SUB RSP, 0x20
                decode_x86_64(&[0x48, 0x83, 0xC4, 0x20], 0x1008), // ADD RSP, 0x20
                decode_x86_64(&[0x5D], 0x100C),                   // POP RBP
                decode_x86_64(&[0xC3], 0x100D),                   // RET
            ],
            true,
        );
        let (blocks, layout) = lift_cfg_semantic(&cfg, LiftArch::X86_64)
            .expect("should lift x86_64 prologue/epilogue");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24);
        assert!(
            matches!(blocks[0].terminator, Terminator::Return),
            "function should terminate with Return"
        );

        // Verify multiple register/SP writes are produced.
        let assign_count =
            blocks[0].stmts.iter().filter(|s| matches!(s, Statement::Assign { .. })).count();
        assert!(
            assign_count >= 6,
            "prologue/epilogue should produce at least 6 Assign statements, got {assign_count}"
        );
    }

    /// Trust: #573 — x86_64 NOP produces only PC advance (no Assign after Nop removal).
    #[test]
    fn test_x86_64_lift_nop_minimal() {
        // 90 = NOP
        // C3 = RET
        let cfg = cfg_with_block(
            vec![decode_x86_64(&[0x90], 0x1000), decode_x86_64(&[0xC3], 0x1001)],
            true,
        );
        let (blocks, layout) =
            lift_cfg_semantic(&cfg, LiftArch::X86_64).expect("should lift x86_64 NOP");
        assert_eq!(blocks.len(), 1);
        assert_eq!(layout.total, 24);

        // NOP produces only a PcUpdate (which becomes an Assign to PC).
        // RET produces MemRead(Nop), SpWrite, Return(empty), PcUpdate -> 2 Assigns.
        // Total non-Nop assigns: at least the PC update from NOP.
        let pc_assigns = blocks[0]
            .stmts
            .iter()
            .filter(
                |s| matches!(s, Statement::Assign { place, .. } if place.local == layout.pc_local),
            )
            .count();
        assert!(pc_assigns >= 1, "NOP should produce at least one PC Assign");
    }
}
