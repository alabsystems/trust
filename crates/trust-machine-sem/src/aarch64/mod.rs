// trust-machine-sem: AArch64 ISA semantics
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

mod fp;
mod helpers;

use trust_disasm::Instruction;
use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{
    BarrierDomain, BarrierType, Condition, MemoryOperand, Operand, RegKind, Register,
};
use trust_types::Formula;

use crate::effect::{
    Aarch64AtomicAccessKind, Aarch64AtomicOrdering, Aarch64SyncBoundaryKind, Aarch64SyncOrdering,
    Aarch64SyncScope, Effect,
};
use crate::error::SemError;
use crate::semantics::Semantics;
use crate::state::MachineState;

use helpers::{compute_nzcv, operand_to_formula, resolve_mem_address};

/// AArch64 instruction semantics.
pub struct Aarch64Semantics;

impl Semantics for Aarch64Semantics {
    fn effects(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        match insn.opcode {
            // Arithmetic
            Opcode::Add | Opcode::Adds => self.sem_add(state, insn),
            Opcode::Sub | Opcode::Subs => self.sem_sub(state, insn),
            Opcode::Adc | Opcode::Adcs => self.sem_adc(state, insn),
            Opcode::Sbc | Opcode::Sbcs => self.sem_sbc(state, insn),
            Opcode::Madd => self.sem_madd(state, insn),
            Opcode::Msub => self.sem_msub(state, insn),
            Opcode::Smaddl | Opcode::Umaddl => self.sem_maddl(state, insn),
            Opcode::Smsubl | Opcode::Umsubl => self.sem_msubl(state, insn),
            Opcode::Smulh | Opcode::Umulh => self.sem_mulh(state, insn),
            Opcode::Udiv => self.sem_udiv(state, insn),
            Opcode::Sdiv => self.sem_sdiv(state, insn),

            // Logic
            Opcode::And | Opcode::Ands => self.sem_and(state, insn),
            Opcode::Orr => self.sem_orr(state, insn),
            Opcode::Eor => self.sem_eor(state, insn),
            Opcode::Bic | Opcode::Bics => self.sem_bic(state, insn),
            Opcode::Orn => self.sem_orn(state, insn),
            Opcode::Eon => self.sem_eon(state, insn),

            // Move
            Opcode::Movz | Opcode::Movn | Opcode::Movk => self.sem_mov_imm(state, insn),

            // Shift (variable)
            Opcode::Lslv => self.sem_shift_var(state, insn),
            Opcode::Lsrv => self.sem_shift_var(state, insn),
            Opcode::Asrv => self.sem_shift_var(state, insn),
            Opcode::Rorv => self.sem_shift_var(state, insn),

            // Bitfield
            Opcode::Ubfm => self.sem_ubfm(state, insn),
            Opcode::Sbfm => self.sem_sbfm(state, insn),
            Opcode::Bfm => self.sem_bfm(state, insn),
            Opcode::Extr => self.sem_extr(state, insn),

            // Bit manipulation
            Opcode::Clz => self.sem_clz(state, insn),
            Opcode::Rbit => self.sem_rbit(state, insn),
            Opcode::Rev => self.sem_rev(state, insn),
            Opcode::Rev16 => self.sem_rev16(state, insn),
            Opcode::Rev32 => self.sem_rev32(state, insn),
            Opcode::Cls => self.sem_cls(state, insn),

            // Conditional select
            Opcode::Csel => self.sem_csel(state, insn),
            Opcode::Csinc => self.sem_csinc(state, insn),
            Opcode::Csinv => self.sem_csinv(state, insn),
            Opcode::Csneg => self.sem_csneg(state, insn),

            // Conditional compare
            Opcode::Ccmp => self.sem_ccmp(state, insn),
            Opcode::Ccmn => self.sem_ccmn(state, insn),

            // Address computation
            Opcode::Adr => self.sem_adr(state, insn),
            Opcode::Adrp => self.sem_adrp(state, insn),

            // Loads
            Opcode::Ldr => self.sem_ldr(state, insn),
            Opcode::Ldrb => self.sem_ldr_variant(state, insn, 1, false),
            Opcode::Ldrh => self.sem_ldr_variant(state, insn, 2, false),
            Opcode::Ldrsb => self.sem_ldr_variant(state, insn, 1, true),
            Opcode::Ldrsh => self.sem_ldr_variant(state, insn, 2, true),
            Opcode::Ldrsw => self.sem_ldr_variant(state, insn, 4, true),
            Opcode::LdrLiteral => Err(aarch64_proof_blocker_error(insn)),
            Opcode::Ldp => self.sem_ldp(state, insn),

            // Stores
            Opcode::Str => self.sem_str(state, insn),
            Opcode::Strb => self.sem_str_variant(state, insn, 1),
            Opcode::Strh => self.sem_str_variant(state, insn, 2),
            Opcode::Stp => self.sem_stp(state, insn),

            // Non-exclusive acquire/release operations have a scalar data
            // plane plus explicit per-access ordering metadata. Exclusive
            // forms still require monitor reservation/status semantics.
            Opcode::Ldar => self.sem_ldar(state, insn),
            Opcode::Stlr => self.sem_stlr(state, insn),
            Opcode::Ldxr | Opcode::Stxr | Opcode::Ldaxr | Opcode::Stlxr => {
                Err(SemError::UnsupportedAtomic {
                    opcode: insn.opcode,
                    detail: aarch64_atomic_unsupported_detail(insn.opcode),
                })
            }

            // Branches
            Opcode::B => self.sem_b(state, insn),
            Opcode::Bl => self.sem_bl(state, insn),
            Opcode::Br => self.sem_br(state, insn),
            Opcode::Blr => self.sem_blr(state, insn),
            Opcode::Ret => self.sem_ret(state, insn),
            Opcode::BCond => self.sem_bcond(state, insn),
            Opcode::Cbz => self.sem_cbz(state, insn, false),
            Opcode::Cbnz => self.sem_cbz(state, insn, true),
            Opcode::Tbz => self.sem_tbz(state, insn, false),
            Opcode::Tbnz => self.sem_tbz(state, insn, true),

            // System / no-ops
            Opcode::Nop | Opcode::Yield | Opcode::Sev | Opcode::Sevl | Opcode::Prfm => Ok(vec![]),
            Opcode::Dmb | Opcode::Dsb | Opcode::Isb | Opcode::Clrex => {
                self.sem_sync_boundary(state, insn)
            }
            Opcode::Svc
            | Opcode::Hvc
            | Opcode::Smc
            | Opcode::Brk
            | Opcode::Hlt
            | Opcode::Mrs
            | Opcode::Msr
            | Opcode::Wfe
            | Opcode::Wfi => Err(aarch64_proof_blocker_error(insn)),

            // FP scalar arithmetic
            Opcode::Fadd => self.sem_fadd(state, insn),
            Opcode::Fsub => self.sem_fsub(state, insn),
            Opcode::Fmul => self.sem_fmul(state, insn),
            Opcode::Fdiv => self.sem_fdiv(state, insn),

            // FP compare
            Opcode::Fcmp => self.sem_fcmp(state, insn),

            // FP move
            Opcode::FmovReg => self.sem_fmov_reg(state, insn),
            Opcode::FmovImm => self.sem_fmov_imm(state, insn),

            // FP unary
            Opcode::Fneg => self.sem_fneg(state, insn),
            Opcode::Fabs => self.sem_fabs(state, insn),
            Opcode::Fsqrt => self.sem_fsqrt(state, insn),

            // FP conversion
            Opcode::Fcvtzs => self.sem_fcvtzs(state, insn),
            Opcode::Fcvtzu => self.sem_fcvtzu(state, insn),
            Opcode::Scvtf => self.sem_scvtf(state, insn),
            Opcode::Ucvtf => self.sem_ucvtf(state, insn),
            Opcode::Fcvt => self.sem_fcvt(state, insn),

            // FP conditional select
            Opcode::Fcsel => self.sem_fcsel(state, insn),
            Opcode::SimdMov => Err(aarch64_proof_blocker_error(insn)),

            other => Err(SemError::UnsupportedOpcode(other)),
        }
    }
}

impl Aarch64Semantics {
    fn sem_sync_boundary(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let boundary = match insn.opcode {
            Opcode::Dmb | Opcode::Dsb => {
                let (scope, ordering, raw_option) = barrier_operand_metadata(insn)?;
                let kind = if insn.opcode == Opcode::Dmb {
                    Aarch64SyncBoundaryKind::DataMemoryBarrier
                } else {
                    Aarch64SyncBoundaryKind::DataSynchronizationBarrier
                };

                Effect::Aarch64SyncBoundary {
                    kind,
                    scope,
                    ordering,
                    clears_exclusive_monitor: false,
                    raw_option: Some(raw_option),
                }
            }
            Opcode::Isb => {
                let (scope, _, raw_option) = barrier_operand_metadata(insn)?;
                Effect::Aarch64SyncBoundary {
                    kind: Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier,
                    scope,
                    ordering: Aarch64SyncOrdering::InstructionStream,
                    clears_exclusive_monitor: false,
                    raw_option: Some(raw_option),
                }
            }
            Opcode::Clrex => Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::ClearExclusiveMonitor,
                scope: Aarch64SyncScope::Local,
                ordering: Aarch64SyncOrdering::None,
                clears_exclusive_monitor: true,
                raw_option: clrex_raw_option(insn),
            },
            other => return Err(SemError::UnsupportedOpcode(other)),
        };

        Ok(vec![boundary, pc_advance(state, insn)])
    }

    /// ADD/ADDS: Rd = Rn + Op2 (optionally setting flags).
    fn sem_add(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Adds;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvAdd(Box::new(rn.clone()), Box::new(op2.clone()), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            let nzcv = compute_nzcv(&rn, &op2, &result, width, false);
            effects.push(nzcv);
        }

        // PC advances by 4
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SUB/SUBS: Rd = Rn - Op2 (optionally setting flags).
    /// CMP is an alias for SUBS with Rd = XZR/WZR.
    fn sem_sub(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Subs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvSub(Box::new(rn.clone()), Box::new(op2.clone()), width);
        let mut effects = Vec::new();

        // Writes to ZR (index 31) are discarded — this is how CMP works. BUT for the
        // non-flag-setting SUB-immediate, register index 31 encodes the STACK POINTER,
        // not ZR (e.g. `sub sp, sp, #16` for frame allocation): that write MUST land.
        // `dst_is_sp` (from operand RegKind::Sp) disambiguates SP from ZR.
        if dst_idx < 31 || dst_is_sp {
            effects.push(write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone()));
        }

        if sets_flags {
            let nzcv = compute_nzcv(&rn, &op2, &result, width, true);
            effects.push(nzcv);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MOVZ: Rd = imm16 << shift
    /// MOVN: Rd = ~(imm16 << shift)
    /// MOVK: Rd[shift+15:shift] = imm16 (keep other bits)
    fn sem_mov_imm(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;

        let imm_val = match insn.operand(1) {
            Some(Operand::Imm(v)) => *v,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected immediate".into(),
                });
            }
        };

        let value = match insn.opcode {
            Opcode::Movz => Formula::BitVec { value: imm_val as i128, width },
            Opcode::Movn => {
                Formula::BvNot(Box::new(Formula::BitVec { value: imm_val as i128, width }), width)
            }
            Opcode::Movk => {
                // Bit-field insert: clear the target 16-bit lane, then OR in
                // the shifted immediate. The decoder pre-shifts the immediate.
                // Extract hw (shift amount / 16) from encoding bits [22:21].
                let hw = (insn.encoding >> 21) & 0x3;
                let shift = hw * 16;
                let existing = state.read_gpr(dst_idx, width);

                // Build inverted mask to clear the 16-bit field.
                let width_mask: i128 = if width == 64 {
                    -1i128 // all ones in 64 bits (0xFFFFFFFFFFFFFFFF as i128)
                } else {
                    (1i128 << width) - 1
                };
                let field_mask = (0xFFFF_i128) << shift;
                let inv_mask = (!field_mask) & width_mask;

                let cleared = Formula::BvAnd(
                    Box::new(existing),
                    Box::new(Formula::BitVec { value: inv_mask, width }),
                    width,
                );
                Formula::BvOr(
                    Box::new(cleared),
                    Box::new(Formula::BitVec { value: imm_val as i128, width }),
                    width,
                )
            }
            _ => unreachable!("sem_mov_imm only handles MOVZ, MOVN, and MOVK"),
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, value)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ORR: Rd = Rn | Op2. MOV (register) is ORR Rd, XZR, Rm.
    fn sem_orr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvOr(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// LDR: Rd = mem[addr]. Load register from memory.
    fn sem_ldr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, _dst_is_sp, width) = extract_dst_reg(insn)?;
        let width_bytes = width / 8;

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };

        let addr = resolve_mem_address(state, mem_op)?;

        // Load width_bytes from byte-addressed memory in little-endian order.
        // Reuse the shared `load_le_bytes` helper so the byte assembly (and its
        // SMT-LIB-correct zero-extension amounts) lives in exactly one place.
        let loaded = load_le_bytes(state, &addr, width_bytes, width);

        let mut effects = vec![
            Effect::MemRead { address: addr.clone(), width_bytes },
            Effect::RegWrite { index: dst_idx, width, value: loaded },
        ];

        // Handle pre/post-index writeback to base register.
        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// STR: mem[addr] = Rt. Store register to memory.
    fn sem_str(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let src = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        let width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => 64,
        };
        let width_bytes = width / 8;

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };

        let addr = resolve_mem_address(state, mem_op)?;

        let mut effects = vec![Effect::MemWrite { address: addr.clone(), value: src, width_bytes }];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// LDAR: acquire load with explicit per-access ordering metadata.
    fn sem_ldar(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width, mem_op) = extract_atomic_reg_mem(insn)?;
        let width_bytes = width / 8;
        let addr = resolve_mem_address(state, mem_op)?;
        let loaded = load_le_bytes(state, &addr, width_bytes, width);

        Ok(vec![
            Effect::Aarch64AtomicAccess {
                kind: Aarch64AtomicAccessKind::Load,
                ordering: Aarch64AtomicOrdering::Acquire,
                address: addr.clone(),
                width_bytes,
                exclusive: false,
            },
            Effect::MemRead { address: addr, width_bytes },
            Effect::RegWrite { index: dst_idx, width, value: loaded },
            pc_advance(state, insn),
        ])
    }

    /// STLR: release store with explicit per-access ordering metadata.
    fn sem_stlr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (_, width, mem_op) = extract_atomic_reg_mem(insn)?;
        let width_bytes = width / 8;
        let addr = resolve_mem_address(state, mem_op)?;
        let value = operand_to_formula(state, insn.operand(0), insn.opcode, 0, width)?;

        Ok(vec![
            Effect::Aarch64AtomicAccess {
                kind: Aarch64AtomicAccessKind::Store,
                ordering: Aarch64AtomicOrdering::Release,
                address: addr.clone(),
                width_bytes,
                exclusive: false,
            },
            Effect::MemWrite { address: addr, value, width_bytes },
            pc_advance(state, insn),
        ])
    }

    /// LDP: Rt, Rt2 = mem[addr], mem[addr + element_size].
    fn sem_ldp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (rt, rt2, width, mem_op) = extract_pair_regs_and_mem(insn)?;
        let width_bytes = width / 8;
        let addr0 = resolve_pair_mem_address(state, insn, mem_op)?;
        let addr1 = offset_addr(&addr0, width_bytes);

        let loaded0 = load_le_bytes(state, &addr0, width_bytes, width);
        let loaded1 = load_le_bytes(state, &addr1, width_bytes, width);

        let mut effects = vec![
            Effect::MemRead { address: addr0.clone(), width_bytes },
            Effect::MemRead { address: addr1.clone(), width_bytes },
            Effect::RegWrite { index: rt.index, width, value: loaded0 },
            Effect::RegWrite { index: rt2.index, width, value: loaded1 },
        ];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// STP: mem[addr], mem[addr + element_size] = Rt, Rt2.
    fn sem_stp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (rt, rt2, width, mem_op) = extract_pair_regs_and_mem(insn)?;
        let width_bytes = width / 8;
        let addr0 = resolve_pair_mem_address(state, insn, mem_op)?;
        let addr1 = offset_addr(&addr0, width_bytes);

        let src0 = read_pair_gpr(state, &rt, width);
        let src1 = read_pair_gpr(state, &rt2, width);

        let mut effects = vec![
            Effect::MemWrite { address: addr0.clone(), value: src0, width_bytes },
            Effect::MemWrite { address: addr1.clone(), value: src1, width_bytes },
        ];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }

        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// B: unconditional branch.
    fn sem_b(&self, _state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        Ok(vec![Effect::Branch { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// BL: branch with link (function call).
    fn sem_bl(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        let return_addr = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        Ok(vec![
            Effect::Call { target: target.clone(), return_addr: return_addr.clone() },
            // X30 = return address
            Effect::RegWrite { index: 30, width: 64, value: return_addr },
            Effect::PcUpdate { value: target },
        ])
    }

    /// BR: branch to register.
    fn sem_br(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        Ok(vec![Effect::Branch { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// RET: return (branch to X30 by default).
    fn sem_ret(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        // RET optionally takes a register operand; defaults to X30.
        let target = if insn.operand_count() > 0 {
            operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?
        } else {
            state.read_gpr(30, 64)
        };
        Ok(vec![Effect::Return { target: target.clone() }, Effect::PcUpdate { value: target }])
    }

    /// B.cond: conditional branch.
    fn sem_bcond(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        // Find the condition operand.
        let condition = insn
            .operands()
            .find_map(|op| if let Operand::Cond(c) = op { Some(*c) } else { None })
            .ok_or_else(|| SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "expected condition operand for B.cond".into(),
            })?;

        Ok(vec![Effect::ConditionalBranch { condition, target, fallthrough }])
    }

    // -----------------------------------------------------------------------
    // Arithmetic: ADC/ADCS, SBC/SBCS, MADD, MSUB, UDIV, SDIV
    // -----------------------------------------------------------------------

    /// ADC/ADCS: Rd = Rn + Rm + C.
    fn sem_adc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Adcs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // C flag zero-extended to width bits.
        let carry = Formula::Ite(
            Box::new(state.flags.c.clone()),
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: 0, width }),
        );
        let sum_no_c = Formula::BvAdd(Box::new(rn.clone()), Box::new(rm.clone()), width);
        let result = Formula::BvAdd(Box::new(sum_no_c), Box::new(carry), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];
        if sets_flags {
            effects.push(compute_nzcv(&rn, &rm, &result, width, false));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SBC/SBCS: Rd = Rn - Rm - !C.
    fn sem_sbc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Sbcs;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // borrow = NOT C, so Rd = Rn - Rm - !C = Rn - Rm - 1 + C
        let borrow = Formula::Ite(
            Box::new(state.flags.c.clone()),
            Box::new(Formula::BitVec { value: 0, width }),
            Box::new(Formula::BitVec { value: 1, width }),
        );
        let diff = Formula::BvSub(Box::new(rn.clone()), Box::new(rm.clone()), width);
        let result = Formula::BvSub(Box::new(diff), Box::new(borrow), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];
        if sets_flags {
            effects.push(compute_nzcv(&rn, &rm, &result, width, true));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MADD: Rd = Ra + (Rn * Rm).
    fn sem_madd(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, width)?;

        let product = Formula::BvMul(Box::new(rn), Box::new(rm), width);
        let result = Formula::BvAdd(Box::new(ra), Box::new(product), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// MSUB: Rd = Ra - (Rn * Rm).
    fn sem_msub(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, width)?;

        let product = Formula::BvMul(Box::new(rn), Box::new(rm), width);
        let result = Formula::BvSub(Box::new(ra), Box::new(product), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SMADDL/UMADDL: Rd = Ra + Extend32(Rn) * Extend32(Rm).
    fn sem_maddl(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        if width != 64 {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "long multiply destination must be 64-bit".into(),
            });
        }

        let rn = widen_long_multiply_operand(state, insn, 1)?;
        let rm = widen_long_multiply_operand(state, insn, 2)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, 64)?;
        let product = Formula::BvMul(Box::new(rn), Box::new(rm), 64);
        let result = Formula::BvAdd(Box::new(ra), Box::new(product), 64);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SMSUBL/UMSUBL: Rd = Ra - Extend32(Rn) * Extend32(Rm).
    fn sem_msubl(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        if width != 64 {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "long multiply destination must be 64-bit".into(),
            });
        }

        let rn = widen_long_multiply_operand(state, insn, 1)?;
        let rm = widen_long_multiply_operand(state, insn, 2)?;
        let ra = operand_to_formula(state, insn.operand(3), insn.opcode, 3, 64)?;
        let product = Formula::BvMul(Box::new(rn), Box::new(rm), 64);
        let result = Formula::BvSub(Box::new(ra), Box::new(product), 64);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SMULH/UMULH: Rd = high 64 bits of Extend64(Rn) * Extend64(Rm).
    fn sem_mulh(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        if width != 64 {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "high multiply destination must be 64-bit".into(),
            });
        }

        let signed = insn.opcode == Opcode::Smulh;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, 64)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, 64)?;
        let rn_wide = extend_bv_to_width(rn, 64, 128, signed);
        let rm_wide = extend_bv_to_width(rm, 64, 128, signed);
        let product = Formula::BvMul(Box::new(rn_wide), Box::new(rm_wide), 128);
        let high = Formula::BvExtract { inner: Box::new(product), high: 127, low: 64 };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, high)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// UDIV: Rd = Rn / Rm (unsigned).
    fn sem_udiv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // AArch64: division by zero produces 0 (not a trap).
        let zero = Formula::BitVec { value: 0, width };
        let is_zero = Formula::Eq(Box::new(rm.clone()), Box::new(zero.clone()));
        let quotient = Formula::BvUDiv(Box::new(rn), Box::new(rm), width);
        let result = Formula::Ite(Box::new(is_zero), Box::new(zero), Box::new(quotient));

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SDIV: Rd = Rn / Rm (signed).
    fn sem_sdiv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let zero = Formula::BitVec { value: 0, width };
        let is_zero = Formula::Eq(Box::new(rm.clone()), Box::new(zero.clone()));
        let quotient = Formula::BvSDiv(Box::new(rn), Box::new(rm), width);
        let result = Formula::Ite(Box::new(is_zero), Box::new(zero), Box::new(quotient));

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Logic: AND/ANDS, EOR, BIC/BICS, ORN, EON
    // -----------------------------------------------------------------------

    /// AND/ANDS: Rd = Rn & Op2.
    fn sem_and(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Ands;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvAnd(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            effects.push(logic_nzcv(&result, width));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EOR: Rd = Rn ^ Op2.
    fn sem_eor(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let result = Formula::BvXor(Box::new(rn), Box::new(op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// BIC/BICS: Rd = Rn & ~Op2.
    fn sem_bic(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let sets_flags = insn.opcode == Opcode::Bics;
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvAnd(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result.clone())];

        if sets_flags {
            effects.push(logic_nzcv(&result, width));
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ORN: Rd = Rn | ~Op2.
    fn sem_orn(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvOr(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EON: Rd = Rn ^ ~Op2.
    fn sem_eon(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let op2 = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        let not_op2 = Formula::BvNot(Box::new(op2), width);
        let result = Formula::BvXor(Box::new(rn), Box::new(not_op2), width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Variable shifts: LSLV, LSRV, ASRV, RORV
    // -----------------------------------------------------------------------

    /// Variable shift: Rd = Rn <shift> (Rm mod width).
    fn sem_shift_var(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;

        // Shift amount is Rm mod width (only low 5/6 bits matter).
        let mod_mask = Formula::BitVec { value: i128::from(width - 1), width };
        let shift_amt = Formula::BvAnd(Box::new(rm), Box::new(mod_mask), width);

        let result = match insn.opcode {
            Opcode::Lslv => Formula::BvShl(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Lsrv => Formula::BvLShr(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Asrv => Formula::BvAShr(Box::new(rn), Box::new(shift_amt), width),
            Opcode::Rorv => {
                // ROR(x, n) = (x >> n) | (x << (width - n))
                let right =
                    Formula::BvLShr(Box::new(rn.clone()), Box::new(shift_amt.clone()), width);
                let complement = Formula::BvSub(
                    Box::new(Formula::BitVec { value: i128::from(width), width }),
                    Box::new(shift_amt),
                    width,
                );
                let left = Formula::BvShl(Box::new(rn), Box::new(complement), width);
                Formula::BvOr(Box::new(right), Box::new(left), width)
            }
            _ => unreachable!("sem_shift_var only handles LSLV, LSRV, ASRV, and RORV"),
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Bitfield: UBFM, SBFM, BFM, EXTR
    // -----------------------------------------------------------------------

    /// UBFM: unsigned bitfield move. Extracts a bitfield and zero-extends.
    /// This covers LSL, LSR, UXTB, UXTH aliases.
    fn sem_ubfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;

        let result = if imms >= immr {
            // Extract bits [imms:immr] and zero-extend.
            let field_width = imms - immr + 1;
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            if field_width == width {
                extracted
            } else {
                // Trust: BvZeroExt's second field is the SMT-LIB `zero_extend`
                // amount (bits ADDED), not the target width. Extending a
                // `field_width`-bit slice up to `width` adds `width - field_width`
                // bits; passing `width` produced a `field_width + width`-bit term
                // (e.g. u16->u64 yielded 80 bits) that crashed the SMT discharge.
                Formula::BvZeroExt(Box::new(extracted), width - field_width)
            }
        } else {
            // LSL alias: imms < immr. Shift left by (width - immr), mask to imms+1 bits.
            let shift = width - immr;

            // Mask to keep only the low (imms+1+shift) bits — but for UBFM the
            // upper bits above position imms+shift are zeroed. Since we shift
            // from a clean source, the result is already correct for the
            // zero-extension semantics.
            Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            )
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SBFM: signed bitfield move. Extracts a bitfield and sign-extends.
    /// Covers ASR and SXTB/SXTH/SXTW aliases.
    fn sem_sbfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;

        let result = if imms >= immr {
            // Extract bits [imms:immr] and sign-extend.
            let field_width = imms - immr + 1;
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            if field_width == width {
                extracted
            } else {
                // Trust: BvSignExt's second field is the SMT-LIB `sign_extend`
                // amount (bits ADDED), not the target width. Sign-extending a
                // `field_width`-bit slice up to `width` adds `width - field_width`
                // bits; passing `width` produced a `field_width + width`-bit term
                // (e.g. i16->i64 yielded 80 bits) that crashed the SMT discharge.
                Formula::BvSignExt(Box::new(extracted), width - field_width)
            }
        } else {
            // ASR alias or shift-insert: shift left then arithmetic shift right.
            let shift = width - immr;

            Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            )
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// BFM: bitfield move. Copies a bitfield into the destination without
    /// clearing other bits.
    fn sem_bfm(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let immr = extract_imm(insn, 2)? as u32;
        let imms = extract_imm(insn, 3)? as u32;
        let existing = state.read_gpr(dst_idx, width);

        // Simple model: extract the field from Rn, insert into Rd.
        // When imms >= immr: extract [imms:immr] from Rn, place at [imms-immr:0] in Rd.
        let result = if imms >= immr {
            let field_width = imms - immr + 1;
            let extracted = Formula::BvExtract { inner: Box::new(rn), high: imms, low: immr };
            let ext_full = Formula::BvZeroExt(Box::new(extracted), width);
            // Mask: clear bits [field_width-1:0] in existing.
            let field_mask = (1i128 << field_width) - 1;
            let width_mask: i128 = if width == 64 { -1i128 } else { (1i128 << width) - 1 };
            let inv = (!field_mask) & width_mask;
            let cleared = Formula::BvAnd(
                Box::new(existing),
                Box::new(Formula::BitVec { value: inv, width }),
                width,
            );
            Formula::BvOr(Box::new(cleared), Box::new(ext_full), width)
        } else {
            // imms < immr: insert at [width-immr+imms : width-immr].
            // Simplified: model as shift + mask + or.
            let shift = width - immr;
            let field_width = imms + 1;
            let shifted = Formula::BvShl(
                Box::new(rn),
                Box::new(Formula::BitVec { value: i128::from(shift), width }),
                width,
            );
            let field_mask = ((1i128 << field_width) - 1) << shift;
            let shifted_masked = Formula::BvAnd(
                Box::new(shifted),
                Box::new(Formula::BitVec { value: field_mask, width }),
                width,
            );
            let width_mask: i128 = if width == 64 { -1i128 } else { (1i128 << width) - 1 };
            let inv = (!field_mask) & width_mask;
            let cleared = Formula::BvAnd(
                Box::new(existing),
                Box::new(Formula::BitVec { value: inv, width }),
                width,
            );
            Formula::BvOr(Box::new(cleared), Box::new(shifted_masked), width)
        };

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// EXTR: Rd = (Rn:Rm) >> lsb. Extract from pair of registers.
    fn sem_extr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let lsb = extract_imm(insn, 3)? as u32;

        if lsb == 0 {
            // Trivial case: result = Rm
            let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, rm)];
            effects.push(pc_advance(state, insn));
            return Ok(effects);
        }

        // Rd = (Rm >> lsb) | (Rn << (width - lsb))
        let low_part = Formula::BvLShr(
            Box::new(rm),
            Box::new(Formula::BitVec { value: i128::from(lsb), width }),
            width,
        );
        let high_part = Formula::BvShl(
            Box::new(rn),
            Box::new(Formula::BitVec { value: i128::from(width - lsb), width }),
            width,
        );
        let result = Formula::BvOr(Box::new(low_part), Box::new(high_part), width);

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Bit manipulation: CLZ, RBIT, REV, REV16, REV32, CLS
    // -----------------------------------------------------------------------

    /// CLZ: count leading zeros. Modeled symbolically with Ite chain.
    fn sem_clz(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Model CLZ as a symbolic uninterpreted-style nested Ite:
        // Check each bit from MSB down. Build an Ite chain:
        // if bit[width-1] then 0 else if bit[width-2] then 1 else ...
        let mut result = Formula::BitVec { value: i128::from(width), width };
        for i in 0..width {
            let bit_pos = i;
            let bit =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: bit_pos, low: bit_pos };
            let is_one =
                Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 1, width: 1 }));
            let clz_val = Formula::BitVec { value: i128::from(width - 1 - bit_pos), width };
            result = Formula::Ite(Box::new(is_one), Box::new(clz_val), Box::new(result));
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// RBIT: reverse bits. Model as building a new value from each bit.
    fn sem_rbit(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Reverse all bits: result[i] = src[width-1-i].
        // Build by extracting each bit, shifting to its reversed position, and OR-ing.
        let mut result = Formula::BitVec { value: 0, width };
        for i in 0..width {
            let src_bit = Formula::BvExtract { inner: Box::new(rn.clone()), high: i, low: i };
            let extended = Formula::BvZeroExt(Box::new(src_bit), width);
            let dest_pos = width - 1 - i;
            if dest_pos > 0 {
                let shifted = Formula::BvShl(
                    Box::new(extended),
                    Box::new(Formula::BitVec { value: i128::from(dest_pos), width }),
                    width,
                );
                result = Formula::BvOr(Box::new(result), Box::new(shifted), width);
            } else {
                result = Formula::BvOr(Box::new(result), Box::new(extended), width);
            }
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV: reverse bytes (full width).
    fn sem_rev(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let result = reverse_bytes(&rn, width, width);
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV16: reverse bytes in each 16-bit halfword.
    fn sem_rev16(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // Swap bytes within each 16-bit lane.
        let num_lanes = width / 16;
        let mut result = Formula::BitVec { value: 0, width };
        for lane in 0..num_lanes {
            let base = lane * 16;
            let lo = Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 7, low: base };
            let hi =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 15, low: base + 8 };
            // Swapped: hi goes to low byte, lo goes to high byte.
            let lo_ext = Formula::BvZeroExt(Box::new(lo), width);
            let hi_ext = Formula::BvZeroExt(Box::new(hi), width);
            let lo_shifted = Formula::BvShl(
                Box::new(lo_ext),
                Box::new(Formula::BitVec { value: i128::from(base + 8), width }),
                width,
            );
            let hi_shifted = Formula::BvShl(
                Box::new(hi_ext),
                Box::new(Formula::BitVec { value: i128::from(base), width }),
                width,
            );
            result = Formula::BvOr(Box::new(result), Box::new(lo_shifted), width);
            result = Formula::BvOr(Box::new(result), Box::new(hi_shifted), width);
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// REV32: reverse bytes in each 32-bit word.
    fn sem_rev32(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        let num_words = width / 32;
        let mut result = Formula::BitVec { value: 0, width };
        for word in 0..num_words {
            let base = word * 32;
            let word_val =
                Formula::BvExtract { inner: Box::new(rn.clone()), high: base + 31, low: base };
            let reversed = reverse_bytes(&word_val, 32, 32);
            let ext = Formula::BvZeroExt(Box::new(reversed), width);
            if base > 0 {
                let shifted = Formula::BvShl(
                    Box::new(ext),
                    Box::new(Formula::BitVec { value: i128::from(base), width }),
                    width,
                );
                result = Formula::BvOr(Box::new(result), Box::new(shifted), width);
            } else {
                result = Formula::BvOr(Box::new(result), Box::new(ext), width);
            }
        }

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CLS: count leading sign bits. Like CLZ but on the XOR of the value with
    /// its sign-extended MSB, then subtract 1.
    fn sem_cls(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;

        // CLS(x) = CLZ(x XOR (x ASR (width-1))) - 1
        // The ASR replicates the sign bit, so XOR flips all sign bits to 0.
        let sign_fill = Formula::BvAShr(
            Box::new(rn.clone()),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let xored = Formula::BvXor(Box::new(rn), Box::new(sign_fill), width);

        // CLZ of xored, then subtract 1.
        // Reuse same Ite-chain approach as CLZ.
        let mut clz_result = Formula::BitVec { value: i128::from(width), width };
        for i in 0..width {
            let bit = Formula::BvExtract { inner: Box::new(xored.clone()), high: i, low: i };
            let is_one =
                Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 1, width: 1 }));
            let clz_val = Formula::BitVec { value: i128::from(width - 1 - i), width };
            clz_result = Formula::Ite(Box::new(is_one), Box::new(clz_val), Box::new(clz_result));
        }

        let result = Formula::BvSub(
            Box::new(clz_result),
            Box::new(Formula::BitVec { value: 1, width }),
            width,
        );

        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Conditional select: CSEL, CSINC, CSINV, CSNEG
    // -----------------------------------------------------------------------

    /// CSEL: Rd = cond ? Rn : Rm.
    fn sem_csel(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSINC: Rd = cond ? Rn : (Rm + 1).
    fn sem_csinc(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let rm_inc =
            Formula::BvAdd(Box::new(rm), Box::new(Formula::BitVec { value: 1, width }), width);
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_inc));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSINV: Rd = cond ? Rn : ~Rm.
    fn sem_csinv(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let rm_inv = Formula::BvNot(Box::new(rm), width);
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_inv));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// CSNEG: Rd = cond ? Rn : -Rm.
    fn sem_csneg(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, width) = extract_dst_reg(insn)?;
        let rn = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let rm = operand_to_formula(state, insn.operand(2), insn.opcode, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        // -Rm = ~Rm + 1 (two's complement negation)
        let rm_neg = Formula::BvAdd(
            Box::new(Formula::BvNot(Box::new(rm), width)),
            Box::new(Formula::BitVec { value: 1, width }),
            width,
        );
        let result = Formula::Ite(Box::new(cond_formula), Box::new(rn), Box::new(rm_neg));
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, width, result)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Conditional compare: CCMP, CCMN
    // -----------------------------------------------------------------------

    /// CCMP: if cond then compare (Rn - Op2) else set NZCV = nzcv_imm.
    fn sem_ccmp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_ccmp_inner(state, insn, true)
    }

    /// CCMN: if cond then compare (Rn + Op2) else set NZCV = nzcv_imm.
    fn sem_ccmn(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        self.sem_ccmp_inner(state, insn, false)
    }

    /// Shared implementation for CCMP/CCMN.
    fn sem_ccmp_inner(
        &self,
        state: &MachineState,
        insn: &Instruction,
        is_sub: bool,
    ) -> Result<Vec<Effect>, SemError> {
        // CCMP/CCMN Rn, #imm5/Rm, #nzcv, cond
        // Operands: 0=Rn, 1=Op2(imm or reg), 2=nzcv_imm, 3=cond
        let width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let rn = operand_to_formula(state, insn.operand(0), insn.opcode, 0, width)?;
        let op2 = operand_to_formula(state, insn.operand(1), insn.opcode, 1, width)?;
        let nzcv_imm = extract_imm(insn, 2)? as u8;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        // Compute comparison result.
        let result = if is_sub {
            Formula::BvSub(Box::new(rn.clone()), Box::new(op2.clone()), width)
        } else {
            Formula::BvAdd(Box::new(rn.clone()), Box::new(op2.clone()), width)
        };
        let flags_computed = compute_nzcv(&rn, &op2, &result, width, is_sub);

        // If condition false, use the immediate NZCV.
        let n_imm = Formula::Bool((nzcv_imm >> 3) & 1 != 0);
        let z_imm = Formula::Bool((nzcv_imm >> 2) & 1 != 0);
        let c_imm = Formula::Bool((nzcv_imm >> 1) & 1 != 0);
        let v_imm = Formula::Bool(nzcv_imm & 1 != 0);

        let (n_comp, z_comp, c_comp, v_comp) = match flags_computed {
            Effect::FlagUpdate { n, z, c, v } => (n, z, c, v),
            _ => unreachable!("compute_nzcv always returns Effect::FlagUpdate"),
        };

        let flags = Effect::FlagUpdate {
            n: Formula::Ite(Box::new(cond_formula.clone()), Box::new(n_comp), Box::new(n_imm)),
            z: Formula::Ite(Box::new(cond_formula.clone()), Box::new(z_comp), Box::new(z_imm)),
            c: Formula::Ite(Box::new(cond_formula.clone()), Box::new(c_comp), Box::new(c_imm)),
            v: Formula::Ite(Box::new(cond_formula), Box::new(v_comp), Box::new(v_imm)),
        };

        Ok(vec![flags, pc_advance(state, insn)])
    }

    // -----------------------------------------------------------------------
    // Address computation: ADR, ADRP
    // -----------------------------------------------------------------------

    /// ADR: Rd = PC + offset.
    fn sem_adr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, _width) = extract_dst_reg(insn)?;
        let target = match insn.operand(1) {
            Some(Operand::PcRelAddr(addr)) => Formula::BitVec { value: *addr as i128, width: 64 },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected PC-relative address".into(),
                });
            }
        };
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, target)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// ADRP: Rd = (PC & ~0xFFF) + (offset << 12). Page-aligned.
    fn sem_adrp(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_is_sp, _width) = extract_dst_reg(insn)?;
        // Decoder resolves ADRP to full target address.
        let target = match insn.operand(1) {
            Some(Operand::PcRelAddr(addr)) => Formula::BitVec { value: *addr as i128, width: 64 },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected PC-relative address".into(),
                });
            }
        };
        let mut effects = vec![write_reg_or_sp(dst_idx, dst_is_sp, 64, target)];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Load/store variants
    // -----------------------------------------------------------------------

    /// Load variant: LDRB (1 byte), LDRH (2 bytes), LDRSB/LDRSH/LDRSW (sign-extending).
    fn sem_ldr_variant(
        &self,
        state: &MachineState,
        insn: &Instruction,
        load_bytes: u32,
        sign_extend: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, _dst_is_sp, width) = extract_dst_reg(insn)?;
        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };
        let addr = resolve_mem_address(state, mem_op)?;

        // Load load_bytes bytes in little-endian order.
        let load_width = load_bytes * 8;
        let loaded = load_le_bytes(state, &addr, load_bytes, load_width);

        // Extend to destination width.
        let extended = if load_width == width {
            loaded
        } else if sign_extend {
            Formula::BvSignExt(Box::new(loaded), width)
        } else {
            Formula::BvZeroExt(Box::new(loaded), width)
        };

        let mut effects = vec![
            Effect::MemRead { address: addr.clone(), width_bytes: load_bytes },
            Effect::RegWrite { index: dst_idx, width, value: extended },
        ];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// Store variant: STRB (1 byte), STRH (2 bytes).
    fn sem_str_variant(
        &self,
        state: &MachineState,
        insn: &Instruction,
        store_bytes: u32,
    ) -> Result<Vec<Effect>, SemError> {
        let store_width = store_bytes * 8;
        let src_full = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        // Truncate to the store width.
        let src = if store_width < 64 {
            Formula::BvExtract { inner: Box::new(src_full), high: store_width - 1, low: 0 }
        } else {
            src_full
        };

        let mem_op = match insn.operand(1) {
            Some(Operand::Mem(m)) => m,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected memory operand".into(),
                });
            }
        };
        let addr = resolve_mem_address(state, mem_op)?;

        let mut effects =
            vec![Effect::MemWrite { address: addr.clone(), value: src, width_bytes: store_bytes }];

        if let Some(wb) = writeback_effect(state, mem_op) {
            effects.push(wb);
        }
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -----------------------------------------------------------------------
    // Branch variants
    // -----------------------------------------------------------------------

    /// BLR: branch with link to register.
    fn sem_blr(&self, state: &MachineState, insn: &Instruction) -> Result<Vec<Effect>, SemError> {
        let target = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;
        let return_addr = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );
        Ok(vec![
            Effect::Call { target: target.clone(), return_addr: return_addr.clone() },
            Effect::RegWrite { index: 30, width: 64, value: return_addr },
            Effect::PcUpdate { value: target },
        ])
    }

    /// CBZ/CBNZ: compare and branch (zero / non-zero).
    fn sem_cbz(
        &self,
        state: &MachineState,
        insn: &Instruction,
        non_zero: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let rt_width = match insn.operand(0) {
            Some(Operand::Reg(r)) => u32::from(r.width),
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let rt = operand_to_formula(state, insn.operand(0), insn.opcode, 0, rt_width)?;
        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        let is_zero =
            Formula::Eq(Box::new(rt), Box::new(Formula::BitVec { value: 0, width: rt_width }));
        let take_branch = if non_zero { Formula::Not(Box::new(is_zero)) } else { is_zero };

        let pc_val = Formula::Ite(Box::new(take_branch), Box::new(target), Box::new(fallthrough));
        Ok(vec![Effect::PcUpdate { value: pc_val }])
    }

    /// TBZ/TBNZ: test bit and branch.
    fn sem_tbz(
        &self,
        state: &MachineState,
        insn: &Instruction,
        non_zero: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let rt = operand_to_formula(state, insn.operand(0), insn.opcode, 0, 64)?;

        // Bit position operand.
        let bit_pos = match insn.operand(1) {
            Some(Operand::BitPos(b)) => u32::from(*b),
            Some(Operand::Imm(v)) => *v as u32,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected bit position".into(),
                });
            }
        };

        let target = branch_target_formula(insn)?;
        let fallthrough = Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        );

        let bit = Formula::BvExtract { inner: Box::new(rt), high: bit_pos, low: bit_pos };
        let is_zero = Formula::Eq(Box::new(bit), Box::new(Formula::BitVec { value: 0, width: 1 }));
        let take_branch = if non_zero { Formula::Not(Box::new(is_zero)) } else { is_zero };

        let pc_val = Formula::Ite(Box::new(take_branch), Box::new(target), Box::new(fallthrough));
        Ok(vec![Effect::PcUpdate { value: pc_val }])
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Extract destination register info from the first operand.
fn extract_dst_reg(insn: &Instruction) -> Result<(u8, bool, u32), SemError> {
    match insn.operand(0) {
        Some(Operand::Reg(r)) => {
            let is_sp = r.kind == RegKind::Sp;
            Ok((r.index, is_sp, u32::from(r.width)))
        }
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "expected register destination".into(),
        }),
    }
}

fn extract_atomic_reg_mem(insn: &Instruction) -> Result<(u8, u32, &MemoryOperand), SemError> {
    let reg = match insn.operand(0) {
        Some(Operand::Reg(reg)) => reg,
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 0,
                detail: "expected atomic register operand".into(),
            });
        }
    };
    let mem = match insn.operand(1) {
        Some(Operand::Mem(mem)) => mem,
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 1,
                detail: "expected atomic memory operand".into(),
            });
        }
    };

    Ok((reg.index, u32::from(reg.width), mem))
}

/// Write to a register or the stack pointer.
fn write_reg_or_sp(index: u8, is_sp: bool, width: u32, value: Formula) -> Effect {
    if is_sp {
        // SP write: zero-extend to 64 bits if width < 64.
        let val64 = if width < 64 { Formula::BvZeroExt(Box::new(value), 64) } else { value };
        Effect::SpWrite { value: val64 }
    } else {
        Effect::RegWrite { index, width, value }
    }
}

fn barrier_operand_metadata(
    insn: &Instruction,
) -> Result<(Aarch64SyncScope, Aarch64SyncOrdering, u8), SemError> {
    match insn.operand(0) {
        Some(Operand::Barrier { domain, kind }) => Ok((
            aarch64_sync_scope(*domain),
            aarch64_sync_ordering(*kind),
            barrier_raw_option(*domain, *kind),
        )),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "expected AArch64 barrier option".into(),
        }),
    }
}

fn aarch64_sync_scope(domain: BarrierDomain) -> Aarch64SyncScope {
    match domain {
        BarrierDomain::Osh => Aarch64SyncScope::OuterShareable,
        BarrierDomain::Nsh => Aarch64SyncScope::NonShareable,
        BarrierDomain::Ish => Aarch64SyncScope::InnerShareable,
        BarrierDomain::Sy => Aarch64SyncScope::FullSystem,
        _ => Aarch64SyncScope::FullSystem,
    }
}

fn aarch64_sync_ordering(kind: BarrierType) -> Aarch64SyncOrdering {
    match kind {
        BarrierType::Ld => Aarch64SyncOrdering::Loads,
        BarrierType::St => Aarch64SyncOrdering::Stores,
        BarrierType::Full => Aarch64SyncOrdering::LoadsAndStores,
        _ => Aarch64SyncOrdering::LoadsAndStores,
    }
}

fn barrier_raw_option(domain: BarrierDomain, kind: BarrierType) -> u8 {
    let domain_bits = match domain {
        BarrierDomain::Osh => 0b00,
        BarrierDomain::Nsh => 0b01,
        BarrierDomain::Ish => 0b10,
        BarrierDomain::Sy => 0b11,
        _ => 0b11,
    };
    let kind_bits = match kind {
        BarrierType::Ld => 0b01,
        BarrierType::St => 0b10,
        BarrierType::Full => 0b11,
        _ => 0b11,
    };
    (domain_bits << 2) | kind_bits
}

fn clrex_raw_option(insn: &Instruction) -> Option<u8> {
    match insn.operand(0) {
        Some(Operand::Imm(value)) => Some((*value & 0xf) as u8),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[trust::skip]
enum Aarch64ExclusiveOrdering {
    Relaxed,
    Acquire,
    Release,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[trust::skip]
enum Aarch64ExclusiveMonitorOperation {
    LoadReserve,
    StoreConditional,
}

#[derive(Debug, Clone, Copy)]
#[trust::skip]
struct Aarch64ExclusiveMonitorEvidence {
    mnemonic: &'static str,
    blocker_code: &'static str,
    access: Aarch64AtomicAccessKind,
    ordering: Aarch64ExclusiveOrdering,
    monitor_operation: Aarch64ExclusiveMonitorOperation,
    reports_status: bool,
    missing_witnesses: &'static [&'static str],
    scalar_data_plane: &'static str,
    unsound_plain_lowering: &'static str,
}

const LDXR_MISSING_WITNESSES: &[&str] =
    &["monitor reservation state", "monitor invalidation", "thread identity"];
const STXR_MISSING_WITNESSES: &[&str] = &[
    "monitor reservation state",
    "monitor invalidation",
    "thread identity",
    "store-conditional status result",
];
const LDAXR_MISSING_WITNESSES: &[&str] = &[
    "acquire ordering event",
    "synchronization edge",
    "monitor reservation state",
    "monitor invalidation",
    "thread identity",
    "happens-before witness",
];
const STLXR_MISSING_WITNESSES: &[&str] = &[
    "release ordering event",
    "synchronization edge",
    "monitor reservation state",
    "monitor invalidation",
    "thread identity",
    "store-conditional status result",
    "happens-before witness",
];
const LDAR_ORDERING_MISSING_WITNESSES: &[&str] = &[
    "acquire ordering event",
    "synchronization edge",
    "thread identity",
    "happens-before witness",
];
const STLR_ORDERING_MISSING_WITNESSES: &[&str] = &[
    "release ordering event",
    "synchronization edge",
    "thread identity",
    "happens-before witness",
];

fn aarch64_exclusive_monitor_evidence(opcode: Opcode) -> Option<Aarch64ExclusiveMonitorEvidence> {
    match opcode {
        Opcode::Ldxr => Some(Aarch64ExclusiveMonitorEvidence {
            mnemonic: "LDXR",
            blocker_code: "aarch64-ldxr-exclusive-monitor-not-proof-consumed",
            access: Aarch64AtomicAccessKind::Load,
            ordering: Aarch64ExclusiveOrdering::Relaxed,
            monitor_operation: Aarch64ExclusiveMonitorOperation::LoadReserve,
            reports_status: false,
            missing_witnesses: LDXR_MISSING_WITNESSES,
            scalar_data_plane: "MemRead+RegWrite plus monitor reservation",
            unsound_plain_lowering: "lowering it as a plain load would drop the exclusive monitor reservation",
        }),
        Opcode::Stxr => Some(Aarch64ExclusiveMonitorEvidence {
            mnemonic: "STXR",
            blocker_code: "aarch64-stxr-exclusive-monitor-status-not-proof-consumed",
            access: Aarch64AtomicAccessKind::Store,
            ordering: Aarch64ExclusiveOrdering::Relaxed,
            monitor_operation: Aarch64ExclusiveMonitorOperation::StoreConditional,
            reports_status: true,
            missing_witnesses: STXR_MISSING_WITNESSES,
            scalar_data_plane: "conditional MemWrite plus status RegWrite",
            unsound_plain_lowering: "lowering it as an unconditional store would be unsound because STXR conditionally stores and reports success",
        }),
        Opcode::Ldaxr => Some(Aarch64ExclusiveMonitorEvidence {
            mnemonic: "LDAXR",
            blocker_code: "aarch64-ldaxr-acquire-exclusive-monitor-not-proof-consumed",
            access: Aarch64AtomicAccessKind::Load,
            ordering: Aarch64ExclusiveOrdering::Acquire,
            monitor_operation: Aarch64ExclusiveMonitorOperation::LoadReserve,
            reports_status: false,
            missing_witnesses: LDAXR_MISSING_WITNESSES,
            scalar_data_plane: "MemRead+RegWrite plus acquire memory ordering plus monitor reservation",
            unsound_plain_lowering: "lowering it as a plain acquire load would drop the exclusive monitor reservation",
        }),
        Opcode::Stlxr => Some(Aarch64ExclusiveMonitorEvidence {
            mnemonic: "STLXR",
            blocker_code: "aarch64-stlxr-release-exclusive-monitor-status-not-proof-consumed",
            access: Aarch64AtomicAccessKind::Store,
            ordering: Aarch64ExclusiveOrdering::Release,
            monitor_operation: Aarch64ExclusiveMonitorOperation::StoreConditional,
            reports_status: true,
            missing_witnesses: STLXR_MISSING_WITNESSES,
            scalar_data_plane: "conditional MemWrite plus release memory ordering plus status RegWrite",
            unsound_plain_lowering: "lowering it as a plain release store would drop both the monitor condition and the status result",
        }),
        _ => None,
    }
}

fn aarch64_atomic_unsupported_detail(opcode: Opcode) -> String {
    if let Some(evidence) = aarch64_exclusive_monitor_evidence(opcode) {
        let witnesses = evidence.missing_witnesses.join(", ");
        return format!(
            "{} exclusive monitor semantics are fail-closed: blocker_code={}; status=not proof-consumed; access={:?}; ordering={:?}; monitor_operation={:?}; reports_status={}; scalar_data_plane={}; missing_witnesses={}; proof-consumed witnesses are required before monitor effects can be emitted; {}",
            evidence.mnemonic,
            evidence.blocker_code,
            evidence.access,
            evidence.ordering,
            evidence.monitor_operation,
            evidence.reports_status,
            evidence.scalar_data_plane,
            witnesses,
            evidence.unsound_plain_lowering
        );
    }

    match opcode {
        Opcode::Ldar => format!(
            "LDAR requires per-access acquire memory ordering; blocker_code=aarch64-ldar-acquire-ordering-not-proof-consumed; status=not proof-consumed; missing_witnesses={}; audit: scalar data-plane is representable as MemRead+RegWrite, but real semantics is blocked until acquire synchronization edges, thread identity, and happens-before witnesses are proof-consumed; lowering it as a plain load would drop ordering constraints",
            LDAR_ORDERING_MISSING_WITNESSES.join(", ")
        ),
        Opcode::Stlr => format!(
            "STLR requires per-access release memory ordering; blocker_code=aarch64-stlr-release-ordering-not-proof-consumed; status=not proof-consumed; missing_witnesses={}; audit: scalar data-plane is representable as MemWrite, but real semantics is blocked until release synchronization edges, thread identity, and happens-before witnesses are proof-consumed; lowering it as a plain store would drop ordering constraints",
            STLR_ORDERING_MISSING_WITNESSES.join(", ")
        ),
        _ => "not an AArch64 atomic/exclusive opcode".to_string(),
    }
}

fn aarch64_proof_blocker_error(insn: &Instruction) -> SemError {
    let (category, detail) = aarch64_proof_blocker_detail(insn);
    SemError::UnsupportedAarch64ProofBlocker { opcode: insn.opcode, category, detail }
}

fn aarch64_proof_blocker_detail(insn: &Instruction) -> (&'static str, String) {
    let evidence = aarch64_opcode_proof_blocker_evidence(insn.opcode);
    let detail = match insn.opcode {
        Opcode::Svc => format!(
            "SVC {} traps to a supervisor/syscall boundary; fail-closed proof blocker: syscall ABI/effect summary, kernel/process state, exception return, and proof-grade witness consumption are not modeled",
            immediate_operand_text(insn)
        ),
        Opcode::Hvc => format!(
            "HVC {} enters a hypervisor boundary; fail-closed proof blocker: EL2 state, call ABI/effect summary, exception return, and proof-grade witness consumption are not modeled",
            immediate_operand_text(insn)
        ),
        Opcode::Smc => format!(
            "SMC {} enters a secure monitor boundary; fail-closed proof blocker: secure monitor state, call ABI/effect summary, exception return, and proof-grade witness consumption are not modeled",
            immediate_operand_text(insn)
        ),
        Opcode::Brk => format!(
            "BRK {} raises a debug exception; fail-closed proof blocker: debug exception control transfer, handler effects, resume state, and proof-grade witness consumption are not modeled",
            immediate_operand_text(insn)
        ),
        Opcode::Hlt => format!(
            "HLT {} raises a halt/debug exception; fail-closed proof blocker: halt handling, privileged/debug state, resume behavior, and proof-grade witness consumption are not modeled",
            immediate_operand_text(insn)
        ),
        Opcode::Mrs => format!(
            "MRS reads architectural system register state ({}) into the scalar data plane; fail-closed proof blocker: typed system-register state, privilege checks, side effects, and proof-grade witnesses are not modeled",
            operand_debug_summary(insn)
        ),
        Opcode::Msr => format!(
            "MSR writes architectural system register state ({}); fail-closed proof blocker: typed system-register state updates, privilege checks, side effects, and proof-grade witnesses are not modeled",
            operand_debug_summary(insn)
        ),
        Opcode::LdrLiteral => format!(
            "LDR literal reads PC-relative literal-pool memory ({}); fail-closed proof blocker: exact PC-relative provenance, relocation/literal-pool bytes, memory snapshot, and proof-grade witnesses are not modeled",
            operand_debug_summary(insn)
        ),
        Opcode::Wfe => {
            "WFE can wait on event state; fail-closed proof blocker: event register state, scheduler/thread identity, wakeup/invalidation conditions, and proof-grade witnesses are not modeled".to_string()
        }
        Opcode::Wfi => {
            "WFI can wait on interrupt state; fail-closed proof blocker: interrupt mask/state, scheduler/thread identity, wakeup conditions, and proof-grade witnesses are not modeled".to_string()
        }
        Opcode::SimdMov => format!(
            "SIMD MOV touches vector/FP architectural state ({}); fail-closed proof blocker: lane layout, vector register state, FP/SIMD side effects, and proof-grade witnesses are not modeled by scalar semantics",
            operand_debug_summary(insn)
        ),
        _ => format!("recognized AArch64 opcode {:?} has no typed proof-blocker detail", insn.opcode),
    };
    (evidence.category, append_proof_blocker_metadata(detail, evidence))
}

#[derive(Debug, Clone, Copy)]
#[trust::skip]
struct Aarch64OpcodeProofBlockerEvidence {
    category: &'static str,
    blocker_code: &'static str,
    missing_witnesses: &'static [&'static str],
}

const SVC_MISSING_WITNESSES: &[&str] =
    &["syscall ABI/effect summary", "kernel/process state", "exception return"];
const HVC_MISSING_WITNESSES: &[&str] =
    &["EL2 state", "call ABI/effect summary", "exception return"];
const SMC_MISSING_WITNESSES: &[&str] =
    &["secure monitor state", "call ABI/effect summary", "exception return"];
const BRK_MISSING_WITNESSES: &[&str] =
    &["debug exception control transfer", "handler effects", "resume state"];
const HLT_MISSING_WITNESSES: &[&str] =
    &["halt handling", "privileged/debug state", "resume behavior"];
const MRS_MISSING_WITNESSES: &[&str] =
    &["typed system-register state", "privilege checks", "side effects"];
const MSR_MISSING_WITNESSES: &[&str] =
    &["typed system-register state updates", "privilege checks", "side effects"];
const LDR_LITERAL_MISSING_WITNESSES: &[&str] =
    &["exact PC-relative provenance", "relocation/literal-pool bytes", "memory snapshot"];
const WFE_MISSING_WITNESSES: &[&str] =
    &["event register state", "scheduler/thread identity", "wakeup/invalidation conditions"];
const WFI_MISSING_WITNESSES: &[&str] =
    &["interrupt mask/state", "scheduler/thread identity", "wakeup conditions"];
const SIMD_MOV_MISSING_WITNESSES: &[&str] =
    &["lane layout", "vector register state", "FP/SIMD side effects"];
const UNCATEGORIZED_PROOF_BLOCKER_MISSING_WITNESSES: &[&str] = &["typed semantic witness category"];

fn aarch64_opcode_proof_blocker_evidence(opcode: Opcode) -> Aarch64OpcodeProofBlockerEvidence {
    match opcode {
        Opcode::Svc => Aarch64OpcodeProofBlockerEvidence {
            category: "trap/syscall",
            blocker_code: "aarch64-svc-trap-not-proof-consumed",
            missing_witnesses: SVC_MISSING_WITNESSES,
        },
        Opcode::Hvc => Aarch64OpcodeProofBlockerEvidence {
            category: "privileged trap",
            blocker_code: "aarch64-hvc-privileged-trap-not-proof-consumed",
            missing_witnesses: HVC_MISSING_WITNESSES,
        },
        Opcode::Smc => Aarch64OpcodeProofBlockerEvidence {
            category: "privileged trap",
            blocker_code: "aarch64-smc-privileged-trap-not-proof-consumed",
            missing_witnesses: SMC_MISSING_WITNESSES,
        },
        Opcode::Brk => Aarch64OpcodeProofBlockerEvidence {
            category: "trap/debug",
            blocker_code: "aarch64-brk-debug-trap-not-proof-consumed",
            missing_witnesses: BRK_MISSING_WITNESSES,
        },
        Opcode::Hlt => Aarch64OpcodeProofBlockerEvidence {
            category: "trap/debug",
            blocker_code: "aarch64-hlt-debug-trap-not-proof-consumed",
            missing_witnesses: HLT_MISSING_WITNESSES,
        },
        Opcode::Mrs => Aarch64OpcodeProofBlockerEvidence {
            category: "system register",
            blocker_code: "aarch64-mrs-system-register-not-proof-consumed",
            missing_witnesses: MRS_MISSING_WITNESSES,
        },
        Opcode::Msr => Aarch64OpcodeProofBlockerEvidence {
            category: "system register",
            blocker_code: "aarch64-msr-system-register-not-proof-consumed",
            missing_witnesses: MSR_MISSING_WITNESSES,
        },
        Opcode::LdrLiteral => Aarch64OpcodeProofBlockerEvidence {
            category: "literal load",
            blocker_code: "aarch64-ldr-literal-pool-not-proof-consumed",
            missing_witnesses: LDR_LITERAL_MISSING_WITNESSES,
        },
        Opcode::Wfe => Aarch64OpcodeProofBlockerEvidence {
            category: "system wait/hint",
            blocker_code: "aarch64-wfe-event-wait-not-proof-consumed",
            missing_witnesses: WFE_MISSING_WITNESSES,
        },
        Opcode::Wfi => Aarch64OpcodeProofBlockerEvidence {
            category: "system wait/hint",
            blocker_code: "aarch64-wfi-interrupt-wait-not-proof-consumed",
            missing_witnesses: WFI_MISSING_WITNESSES,
        },
        Opcode::SimdMov => Aarch64OpcodeProofBlockerEvidence {
            category: "FP/SIMD",
            blocker_code: "aarch64-simd-mov-state-not-proof-consumed",
            missing_witnesses: SIMD_MOV_MISSING_WITNESSES,
        },
        _ => Aarch64OpcodeProofBlockerEvidence {
            category: "uncategorized",
            blocker_code: "aarch64-uncategorized-proof-blocker",
            missing_witnesses: UNCATEGORIZED_PROOF_BLOCKER_MISSING_WITNESSES,
        },
    }
}

fn append_proof_blocker_metadata(
    detail: String,
    evidence: Aarch64OpcodeProofBlockerEvidence,
) -> String {
    format!(
        "{detail}; blocker_code={}; status=not proof-consumed; missing_witnesses={}",
        evidence.blocker_code,
        evidence.missing_witnesses.join(", ")
    )
}

fn immediate_operand_text(insn: &Instruction) -> String {
    match insn.operand(0) {
        Some(Operand::Imm(value)) => format!("#{value}"),
        Some(Operand::SignedImm(value)) => format!("#{value}"),
        _ => "without decoded immediate".to_string(),
    }
}

fn operand_debug_summary(insn: &Instruction) -> String {
    let operands: Vec<String> = insn.operands().map(|operand| format!("{operand:?}")).collect();
    if operands.is_empty() { "no decoded operands".to_string() } else { operands.join(", ") }
}

fn extract_pair_regs_and_mem(
    insn: &Instruction,
) -> Result<(Register, Register, u32, &MemoryOperand), SemError> {
    let rt = extract_pair_gpr(insn, 0)?;
    let rt2 = extract_pair_gpr(insn, 1)?;
    let width = u32::from(rt.width);

    if rt2.width != rt.width {
        return Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 1,
            detail: "LDP/STP register widths must match".into(),
        });
    }

    if width != 32 && width != 64 {
        return Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "LDP/STP supports only 32-bit and 64-bit GPR pairs".into(),
        });
    }

    let mem = match insn.operand(2) {
        Some(Operand::Mem(mem)) => mem,
        _ => {
            return Err(SemError::InvalidOperand {
                opcode: insn.opcode,
                index: 2,
                detail: "expected memory operand".into(),
            });
        }
    };

    Ok((rt, rt2, width, mem))
}

fn extract_pair_gpr(insn: &Instruction, index: usize) -> Result<Register, SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(reg)) if reg.kind == RegKind::Gpr || reg.kind == RegKind::Zr => Ok(*reg),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected GPR pair register".into(),
        }),
    }
}

fn resolve_pair_mem_address(
    state: &MachineState,
    insn: &Instruction,
    mem_op: &MemoryOperand,
) -> Result<Formula, SemError> {
    match mem_op {
        MemoryOperand::Base { .. }
        | MemoryOperand::BaseOffset { .. }
        | MemoryOperand::PreIndex { .. }
        | MemoryOperand::PostIndex { .. } => resolve_mem_address(state, mem_op),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 2,
            detail: "unsupported LDP/STP addressing mode".into(),
        }),
    }
}

fn offset_addr(addr: &Formula, offset_bytes: u32) -> Formula {
    Formula::BvAdd(
        Box::new(addr.clone()),
        Box::new(Formula::BitVec { value: i128::from(offset_bytes), width: 64 }),
        64,
    )
}

fn read_pair_gpr(state: &MachineState, reg: &Register, width: u32) -> Formula {
    if reg.kind == RegKind::Zr {
        Formula::BitVec { value: 0, width }
    } else {
        state.read_gpr(reg.index, width)
    }
}

fn widen_long_multiply_operand(
    state: &MachineState,
    insn: &Instruction,
    index: usize,
) -> Result<Formula, SemError> {
    let signed = matches!(insn.opcode, Opcode::Smaddl | Opcode::Smsubl);
    let value = operand_to_formula(state, insn.operand(index), insn.opcode, index, 32)?;
    Ok(extend_bv_to_width(value, 32, 64, signed))
}

fn extend_bv_to_width(value: Formula, from_width: u32, to_width: u32, signed: bool) -> Formula {
    if to_width <= from_width {
        value
    } else if signed {
        Formula::BvSignExt(Box::new(value), to_width - from_width)
    } else {
        Formula::BvZeroExt(Box::new(value), to_width - from_width)
    }
}

/// PC = PC + 4 (standard sequential advance).
fn pc_advance(state: &MachineState, _insn: &Instruction) -> Effect {
    Effect::PcUpdate {
        value: Formula::BvAdd(
            Box::new(state.pc.clone()),
            Box::new(Formula::BitVec { value: 4, width: 64 }),
            64,
        ),
    }
}

/// Extract a branch target address as a Formula.
fn branch_target_formula(insn: &Instruction) -> Result<Formula, SemError> {
    for op in insn.operands() {
        if let Operand::PcRelAddr(addr) = op {
            return Ok(Formula::BitVec { value: *addr as i128, width: 64 });
        }
    }
    Err(SemError::InvalidOperand {
        opcode: insn.opcode,
        index: 0,
        detail: "no branch target found".into(),
    })
}

/// Compute a writeback effect for pre/post-indexed addressing.
fn writeback_effect(state: &MachineState, mem_op: &MemoryOperand) -> Option<Effect> {
    match mem_op {
        MemoryOperand::PreIndex { base, offset } | MemoryOperand::PostIndex { base, offset } => {
            let base_val = if base.kind == RegKind::Sp {
                state.read_sp(64)
            } else {
                state.read_gpr(base.index, 64)
            };
            let new_val = Formula::BvAdd(
                Box::new(base_val),
                Box::new(Formula::BitVec { value: *offset as i128, width: 64 }),
                64,
            );
            if base.kind == RegKind::Sp {
                Some(Effect::SpWrite { value: new_val })
            } else {
                Some(Effect::RegWrite { index: base.index, width: 64, value: new_val })
            }
        }
        _ => None,
    }
}

/// Compute NZCV for logical operations (AND, BIC, etc.).
/// C and V are set to zero; N and Z are derived from the result.
fn logic_nzcv(result: &Formula, width: u32) -> Effect {
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
    Effect::FlagUpdate { n, z, c: Formula::Bool(false), v: Formula::Bool(false) }
}

/// Extract an immediate value from an operand.
fn extract_imm(insn: &Instruction, index: usize) -> Result<u64, SemError> {
    match insn.operand(index) {
        Some(Operand::Imm(v)) => Ok(*v),
        Some(Operand::SignedImm(v)) => Ok(*v as u64),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected immediate".into(),
        }),
    }
}

/// Extract a condition code from an operand.
fn extract_condition(insn: &Instruction, index: usize) -> Result<Condition, SemError> {
    match insn.operand(index) {
        Some(Operand::Cond(c)) => Ok(*c),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected condition".into(),
        }),
    }
}

/// Convert a `Condition` to a boolean Formula based on the current flags.
// Trust: #564 — made public so semantic_lift can build branch condition formulas.
pub fn condition_to_formula(state: &MachineState, cond: Condition) -> Formula {
    let n = &state.flags.n;
    let z = &state.flags.z;
    let c = &state.flags.c;
    let v = &state.flags.v;
    match cond {
        Condition::Eq => z.clone(),                         // Z == 1
        Condition::Ne => Formula::Not(Box::new(z.clone())), // Z == 0
        Condition::Cs => c.clone(),                         // C == 1 (HS)
        Condition::Cc => Formula::Not(Box::new(c.clone())), // C == 0 (LO)
        Condition::Mi => n.clone(),                         // N == 1
        Condition::Pl => Formula::Not(Box::new(n.clone())), // N == 0
        Condition::Vs => v.clone(),                         // V == 1
        Condition::Vc => Formula::Not(Box::new(v.clone())), // V == 0
        Condition::Hi => {
            // C == 1 && Z == 0
            Formula::And(vec![c.clone(), Formula::Not(Box::new(z.clone()))])
        }
        Condition::Ls => {
            // C == 0 || Z == 1
            Formula::Or(vec![Formula::Not(Box::new(c.clone())), z.clone()])
        }
        Condition::Ge => {
            // N == V
            Formula::Eq(Box::new(n.clone()), Box::new(v.clone()))
        }
        Condition::Lt => {
            // N != V
            Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone()))))
        }
        Condition::Gt => {
            // Z == 0 && N == V
            Formula::And(vec![
                Formula::Not(Box::new(z.clone())),
                Formula::Eq(Box::new(n.clone()), Box::new(v.clone())),
            ])
        }
        Condition::Le => {
            // Z == 1 || N != V
            Formula::Or(vec![
                z.clone(),
                Formula::Not(Box::new(Formula::Eq(Box::new(n.clone()), Box::new(v.clone())))),
            ])
        }
        Condition::Al | Condition::Nv => Formula::Bool(true),
        _ => Formula::Bool(true), // future condition codes
    }
}

/// Reverse bytes within a value of the given width, producing a result of
/// result_width bits.
fn reverse_bytes(val: &Formula, val_width: u32, result_width: u32) -> Formula {
    let num_bytes = val_width / 8;
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for i in 0..num_bytes {
        let src_byte =
            Formula::BvExtract { inner: Box::new(val.clone()), high: i * 8 + 7, low: i * 8 };
        let dest_pos = (num_bytes - 1 - i) * 8;
        // `src_byte` is 8 bits; widen to `result_width` by ADDING
        // `result_width - 8` bits (BvZeroExt's second field is the SMT-LIB
        // `zero_extend` amount, not the target width).
        let extended = Formula::BvZeroExt(Box::new(src_byte), result_width - 8);
        if dest_pos > 0 {
            let shifted = Formula::BvShl(
                Box::new(extended),
                Box::new(Formula::BitVec { value: i128::from(dest_pos), width: result_width }),
                result_width,
            );
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        } else {
            result = Formula::BvOr(Box::new(result), Box::new(extended), result_width);
        }
    }
    result
}

/// Load `num_bytes` from byte-addressed memory in little-endian order,
/// producing a bitvector of `result_width` bits.
fn load_le_bytes(
    state: &MachineState,
    addr: &Formula,
    num_bytes: u32,
    result_width: u32,
) -> Formula {
    let mut result = Formula::BitVec { value: 0, width: result_width };
    for i in 0..num_bytes {
        let byte_addr = if i == 0 {
            addr.clone()
        } else {
            Formula::BvAdd(
                Box::new(addr.clone()),
                Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                64,
            )
        };
        let byte_val = Formula::Select(Box::new(state.memory.clone()), Box::new(byte_addr));
        // A memory byte is 8 bits; widen it to `result_width` by ADDING
        // `result_width - 8` bits. `BvZeroExt`'s second field is the
        // SMT-LIB `zero_extend` amount (bits added), not the target width, so
        // the produced formula is width-correct for the SMT discharge as well
        // as the concrete evaluator (which tolerates either convention).
        let extended = Formula::BvZeroExt(Box::new(byte_val), result_width - 8);
        if i == 0 {
            result = extended;
        } else {
            let shift_amt = Formula::BitVec { value: i128::from(i * 8), width: result_width };
            let shifted = Formula::BvShl(Box::new(extended), Box::new(shift_amt), result_width);
            result = Formula::BvOr(Box::new(result), Box::new(shifted), result_width);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::Semantics;
    use trust_disasm::decode_aarch64;

    fn decode(enc: u32) -> Instruction {
        decode_aarch64(&enc.to_le_bytes(), 0x1000).expect("decode AArch64 instruction")
    }

    fn fallthrough_insn_with_opcode(encoding: u32, opcode: Opcode) -> Instruction {
        let mut insn = decode(0xD503_201F); // NOP shell; operands are irrelevant for fail-closed cases.
        insn.encoding = encoding;
        insn.bytes = encoding.to_le_bytes().to_vec();
        insn.opcode = opcode;
        insn
    }

    fn add64(lhs: Formula, rhs: i128) -> Formula {
        Formula::BvAdd(Box::new(lhs), Box::new(Formula::BitVec { value: rhs, width: 64 }), 64)
    }

    fn pc_plus_4(state: &MachineState) -> Formula {
        add64(state.pc.clone(), 4)
    }

    #[test]
    fn ldp_base_offset_reads_pair_and_writes_gprs() {
        // LDP X0, X1, [X2]
        let insn = decode(0xA9_40_04_40);
        assert_eq!(insn.opcode, Opcode::Ldp);

        let state = MachineState::symbolic();
        let effects = Aarch64Semantics.effects(&state, &insn).expect("LDP effects");

        let addr0 = add64(state.read_gpr(2, 64), 0);
        let addr1 = add64(addr0.clone(), 8);
        let loaded0 = load_le_bytes(&state, &addr0, 8, 64);
        let loaded1 = load_le_bytes(&state, &addr1, 8, 64);

        assert_eq!(
            effects,
            vec![
                Effect::MemRead { address: addr0, width_bytes: 8 },
                Effect::MemRead { address: addr1, width_bytes: 8 },
                Effect::RegWrite { index: 0, width: 64, value: loaded0 },
                Effect::RegWrite { index: 1, width: 64, value: loaded1 },
                Effect::PcUpdate { value: pc_plus_4(&state) },
            ]
        );
    }

    /// Compute the SMT-LIB bit width of a `Formula`, returning `None` for a
    /// non-bitvector node or on any width inconsistency (e.g. a `BvOr` whose
    /// operands disagree, or a `BvShl` with mismatched value/shift widths).
    /// This is the same well-formedness ay enforces, so a formula that passes
    /// here is one ay's bitvector translator will accept.
    fn smt_bv_width(f: &Formula) -> Option<u32> {
        match f {
            Formula::BitVec { width, .. } => Some(*width),
            Formula::Var(_, trust_types::Sort::BitVec(w)) => Some(*w),
            Formula::Select(_, _) => Some(8), // memory element sort is BitVec(8)
            Formula::BvZeroExt(a, n) | Formula::BvSignExt(a, n) => {
                smt_bv_width(a).map(|w| w + n)
            }
            Formula::BvExtract { high, low, .. } => Some(high - low + 1),
            Formula::BvAdd(a, b, w)
            | Formula::BvSub(a, b, w)
            | Formula::BvOr(a, b, w)
            | Formula::BvAnd(a, b, w)
            | Formula::BvShl(a, b, w) => {
                let wa = smt_bv_width(a)?;
                let wb = smt_bv_width(b)?;
                if wa == *w && wb == *w { Some(*w) } else { None }
            }
            _ => None,
        }
    }

    #[test]
    fn load_le_bytes_is_smt_width_consistent() {
        // A 4-byte (i32) load and an 8-byte (i64) load must each produce a
        // Formula whose SMT-LIB widths are internally consistent. Before the
        // fix, the per-byte BvZeroExt used the TARGET width as the extension
        // AMOUNT, producing 8 + result_width-bit subterms that ay's bitvector
        // translator rejects (SortMismatch on the following BvShl/BvOr). This
        // is the regression guard for the store-then-load proof rung.
        let state = MachineState::symbolic();
        let addr = state.read_gpr(0, 64);

        let load32 = load_le_bytes(&state, &addr, 4, 32);
        assert_eq!(
            smt_bv_width(&load32),
            Some(32),
            "4-byte load formula is not SMT-LIB width-consistent: {load32:?}"
        );

        let load64 = load_le_bytes(&state, &addr, 8, 64);
        assert_eq!(
            smt_bv_width(&load64),
            Some(64),
            "8-byte load formula is not SMT-LIB width-consistent: {load64:?}"
        );
    }

    #[test]
    fn stp_pre_index_stores_pair_and_updates_sp() {
        // STP X29, X30, [SP, #-16]!
        let insn = decode(0xA9_BF_7B_FD);
        assert_eq!(insn.opcode, Opcode::Stp);

        let state = MachineState::symbolic();
        let effects = Aarch64Semantics.effects(&state, &insn).expect("STP effects");

        let addr0 = add64(state.sp.clone(), -16);
        let addr1 = add64(addr0.clone(), 8);

        assert_eq!(
            effects,
            vec![
                Effect::MemWrite {
                    address: addr0.clone(),
                    value: state.read_gpr(29, 64),
                    width_bytes: 8,
                },
                Effect::MemWrite { address: addr1, value: state.read_gpr(30, 64), width_bytes: 8 },
                Effect::SpWrite { value: addr0 },
                Effect::PcUpdate { value: pc_plus_4(&state) },
            ]
        );
    }

    #[test]
    fn ldp_post_index_reads_pair_and_updates_sp() {
        // LDP X29, X30, [SP], #16
        let insn = decode(0xA8_C1_7B_FD);
        assert_eq!(insn.opcode, Opcode::Ldp);

        let state = MachineState::symbolic();
        let effects = Aarch64Semantics.effects(&state, &insn).expect("LDP effects");

        let addr0 = state.sp.clone();
        let addr1 = add64(addr0.clone(), 8);
        let loaded0 = load_le_bytes(&state, &addr0, 8, 64);
        let loaded1 = load_le_bytes(&state, &addr1, 8, 64);
        let writeback = add64(state.sp.clone(), 16);

        assert_eq!(
            effects,
            vec![
                Effect::MemRead { address: addr0, width_bytes: 8 },
                Effect::MemRead { address: addr1, width_bytes: 8 },
                Effect::RegWrite { index: 29, width: 64, value: loaded0 },
                Effect::RegWrite { index: 30, width: 64, value: loaded1 },
                Effect::SpWrite { value: writeback },
                Effect::PcUpdate { value: pc_plus_4(&state) },
            ]
        );
    }

    fn only_sync_and_pc_effects(effects: &[Effect]) -> bool {
        effects.iter().all(|effect| {
            matches!(effect, Effect::Aarch64SyncBoundary { .. } | Effect::PcUpdate { .. })
        })
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct EffectProofConsumerBlocker {
        category: &'static str,
        blocker_code: &'static str,
        missing_witnesses: &'static [&'static str],
        scalar_data_plane_represented: bool,
    }

    const DMB_DSB_MISSING_WITNESSES: &[&str] = &[
        "barrier ordering event",
        "shareability scope propagation",
        "memory-system visibility/completion",
        "happens-before witness",
    ];
    const ISB_MISSING_WITNESSES: &[&str] = &[
        "instruction-stream synchronization event",
        "context synchronization witness",
        "pipeline flush witness",
    ];
    const CLREX_EFFECT_MISSING_WITNESSES: &[&str] =
        &["exclusive-monitor state", "thread identity", "monitor clear witness"];
    const FP_WRITE_MISSING_WITNESSES: &[&str] = &[
        "FP/SIMD local layout",
        "IEEE-754 value semantics",
        "FPCR/FPSR state",
        "rounding mode and exception flags",
    ];

    fn effect_proof_consumer_blocker(effect: &Effect) -> Option<EffectProofConsumerBlocker> {
        match effect {
            Effect::Aarch64AtomicAccess {
                kind: Aarch64AtomicAccessKind::Load,
                ordering: Aarch64AtomicOrdering::Acquire,
                exclusive: false,
                ..
            } => Some(EffectProofConsumerBlocker {
                category: "AArch64 acquire/release ordering",
                blocker_code: "aarch64-ldar-acquire-ordering-not-proof-consumed",
                missing_witnesses: LDAR_ORDERING_MISSING_WITNESSES,
                scalar_data_plane_represented: true,
            }),
            Effect::Aarch64AtomicAccess {
                kind: Aarch64AtomicAccessKind::Store,
                ordering: Aarch64AtomicOrdering::Release,
                exclusive: false,
                ..
            } => Some(EffectProofConsumerBlocker {
                category: "AArch64 acquire/release ordering",
                blocker_code: "aarch64-stlr-release-ordering-not-proof-consumed",
                missing_witnesses: STLR_ORDERING_MISSING_WITNESSES,
                scalar_data_plane_represented: true,
            }),
            Effect::Aarch64AtomicAccess { exclusive: true, .. } => {
                Some(EffectProofConsumerBlocker {
                    category: "AArch64 exclusive monitor",
                    blocker_code: "aarch64-exclusive-monitor-not-proof-consumed",
                    missing_witnesses: LDXR_MISSING_WITNESSES,
                    scalar_data_plane_represented: false,
                })
            }
            Effect::Aarch64SyncBoundary {
                kind:
                    Aarch64SyncBoundaryKind::DataMemoryBarrier
                    | Aarch64SyncBoundaryKind::DataSynchronizationBarrier,
                ..
            } => Some(EffectProofConsumerBlocker {
                category: "AArch64 synchronization boundary",
                blocker_code: "aarch64-data-barrier-not-proof-consumed",
                missing_witnesses: DMB_DSB_MISSING_WITNESSES,
                scalar_data_plane_represented: false,
            }),
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier,
                ..
            } => Some(EffectProofConsumerBlocker {
                category: "AArch64 synchronization boundary",
                blocker_code: "aarch64-instruction-barrier-not-proof-consumed",
                missing_witnesses: ISB_MISSING_WITNESSES,
                scalar_data_plane_represented: false,
            }),
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::ClearExclusiveMonitor,
                ..
            } => Some(EffectProofConsumerBlocker {
                category: "AArch64 exclusive monitor",
                blocker_code: "aarch64-clrex-monitor-clear-not-proof-consumed",
                missing_witnesses: CLREX_EFFECT_MISSING_WITNESSES,
                scalar_data_plane_represented: false,
            }),
            Effect::FpRegWrite { .. } => Some(EffectProofConsumerBlocker {
                category: "AArch64 FP/SIMD",
                blocker_code: "aarch64-fp-register-write-not-proof-consumed",
                missing_witnesses: FP_WRITE_MISSING_WITNESSES,
                scalar_data_plane_represented: false,
            }),
            _ => None,
        }
    }

    fn assert_effect_blocker(
        effect: &Effect,
        expected_code: &str,
        expected_missing_witnesses: &[&str],
    ) {
        let blocker = effect_proof_consumer_blocker(effect)
            .unwrap_or_else(|| panic!("expected proof-consumer blocker for {effect:?}"));
        assert_eq!(blocker.blocker_code, expected_code);
        assert_eq!(blocker.missing_witnesses, expected_missing_witnesses);
    }

    #[test]
    fn aarch64_dmb_emits_ordering_scope_boundary_effect() {
        let state = MachineState::symbolic();
        let insn = decode(0xD503_3B9F); // DMB ISH

        let effects = Aarch64Semantics.effects(&state, &insn).expect("DMB effects");

        assert_eq!(effects.len(), 2);
        assert!(only_sync_and_pc_effects(&effects));
        assert_eq!(
            effects[0],
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::DataMemoryBarrier,
                scope: Aarch64SyncScope::InnerShareable,
                ordering: Aarch64SyncOrdering::LoadsAndStores,
                clears_exclusive_monitor: false,
                raw_option: Some(0xB),
            }
        );
        assert_eq!(effects[1], Effect::PcUpdate { value: pc_plus_4(&state) });
    }

    #[test]
    fn aarch64_dsb_emits_data_synchronization_boundary_effect() {
        let state = MachineState::symbolic();
        let insn = decode(0xD503_3F3F); // DSB SY

        let effects = Aarch64Semantics.effects(&state, &insn).expect("DSB effects");

        assert_eq!(effects.len(), 2);
        assert!(only_sync_and_pc_effects(&effects));
        assert_eq!(
            effects[0],
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::DataSynchronizationBarrier,
                scope: Aarch64SyncScope::FullSystem,
                ordering: Aarch64SyncOrdering::LoadsAndStores,
                clears_exclusive_monitor: false,
                raw_option: Some(0xF),
            }
        );
    }

    #[test]
    fn aarch64_isb_emits_instruction_synchronization_boundary_effect() {
        let state = MachineState::symbolic();
        let insn = decode(0xD503_3FDF); // ISB SY

        let effects = Aarch64Semantics.effects(&state, &insn).expect("ISB effects");

        assert_eq!(effects.len(), 2);
        assert!(only_sync_and_pc_effects(&effects));
        assert_eq!(
            effects[0],
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::InstructionSynchronizationBarrier,
                scope: Aarch64SyncScope::FullSystem,
                ordering: Aarch64SyncOrdering::InstructionStream,
                clears_exclusive_monitor: false,
                raw_option: Some(0xF),
            }
        );
    }

    #[test]
    fn aarch64_clrex_emits_monitor_clear_boundary_effect() {
        let state = MachineState::symbolic();
        let insn = decode(0xD503_305F); // CLREX #0

        let effects = Aarch64Semantics.effects(&state, &insn).expect("CLREX effects");

        assert_eq!(effects.len(), 2);
        assert!(only_sync_and_pc_effects(&effects));
        assert_eq!(
            effects[0],
            Effect::Aarch64SyncBoundary {
                kind: Aarch64SyncBoundaryKind::ClearExclusiveMonitor,
                scope: Aarch64SyncScope::Local,
                ordering: Aarch64SyncOrdering::None,
                clears_exclusive_monitor: true,
                raw_option: Some(0),
            }
        );
    }

    #[test]
    fn aarch64_sync_boundaries_carry_unconsumed_proof_blocker_metadata() {
        let state = MachineState::symbolic();
        let cases = [
            (
                0xD503_3B9F,
                Opcode::Dmb,
                "aarch64-data-barrier-not-proof-consumed",
                DMB_DSB_MISSING_WITNESSES,
            ),
            (
                0xD503_3F3F,
                Opcode::Dsb,
                "aarch64-data-barrier-not-proof-consumed",
                DMB_DSB_MISSING_WITNESSES,
            ),
            (
                0xD503_3FDF,
                Opcode::Isb,
                "aarch64-instruction-barrier-not-proof-consumed",
                ISB_MISSING_WITNESSES,
            ),
            (
                0xD503_305F,
                Opcode::Clrex,
                "aarch64-clrex-monitor-clear-not-proof-consumed",
                CLREX_EFFECT_MISSING_WITNESSES,
            ),
        ];

        for (encoding, opcode, expected_code, expected_missing_witnesses) in cases {
            let insn = decode(encoding);
            assert_eq!(insn.opcode, opcode);

            let effects = Aarch64Semantics.effects(&state, &insn).expect("sync effects");
            assert!(only_sync_and_pc_effects(&effects));
            assert_effect_blocker(&effects[0], expected_code, expected_missing_witnesses);
        }
    }

    #[test]
    fn ldar_emits_acquire_metadata_and_scalar_load_effects() {
        let state = MachineState::symbolic();
        let insn = decode(0xC8_DF_FC_20); // LDAR X0, [X1]
        assert_eq!(insn.opcode, Opcode::Ldar);

        let effects = Aarch64Semantics.effects(&state, &insn).expect("LDAR effects");
        let addr = state.read_gpr(1, 64);
        let loaded = load_le_bytes(&state, &addr, 8, 64);

        assert_eq!(
            effects,
            vec![
                Effect::Aarch64AtomicAccess {
                    kind: Aarch64AtomicAccessKind::Load,
                    ordering: Aarch64AtomicOrdering::Acquire,
                    address: addr.clone(),
                    width_bytes: 8,
                    exclusive: false,
                },
                Effect::MemRead { address: addr, width_bytes: 8 },
                Effect::RegWrite { index: 0, width: 64, value: loaded },
                Effect::PcUpdate { value: pc_plus_4(&state) },
            ]
        );
        assert!(
            !effects.iter().any(|effect| matches!(effect, Effect::Aarch64SyncBoundary { .. })),
            "LDAR should carry per-access acquire metadata, not a standalone barrier"
        );
    }

    #[test]
    fn stlr_emits_release_metadata_and_scalar_store_effects() {
        let state = MachineState::symbolic();
        let insn = decode(0xC8_9F_FC_20); // STLR X0, [X1]
        assert_eq!(insn.opcode, Opcode::Stlr);

        let effects = Aarch64Semantics.effects(&state, &insn).expect("STLR effects");
        let addr = state.read_gpr(1, 64);

        assert_eq!(
            effects,
            vec![
                Effect::Aarch64AtomicAccess {
                    kind: Aarch64AtomicAccessKind::Store,
                    ordering: Aarch64AtomicOrdering::Release,
                    address: addr.clone(),
                    width_bytes: 8,
                    exclusive: false,
                },
                Effect::MemWrite { address: addr, value: state.read_gpr(0, 64), width_bytes: 8 },
                Effect::PcUpdate { value: pc_plus_4(&state) },
            ]
        );
        assert!(
            !effects.iter().any(|effect| matches!(effect, Effect::Aarch64SyncBoundary { .. })),
            "STLR should carry per-access release metadata, not a standalone barrier"
        );
    }

    #[test]
    fn ldar_stlr_metadata_remains_unconsumed_proof_blocker_while_data_plane_is_explicit() {
        let state = MachineState::symbolic();
        let cases = [
            (
                0xC8_DF_FC_20,
                Opcode::Ldar,
                "aarch64-ldar-acquire-ordering-not-proof-consumed",
                LDAR_ORDERING_MISSING_WITNESSES,
            ),
            (
                0xC8_9F_FC_20,
                Opcode::Stlr,
                "aarch64-stlr-release-ordering-not-proof-consumed",
                STLR_ORDERING_MISSING_WITNESSES,
            ),
        ];

        for (encoding, opcode, expected_code, expected_missing_witnesses) in cases {
            let insn = decode(encoding);
            assert_eq!(insn.opcode, opcode);

            let effects = Aarch64Semantics.effects(&state, &insn).expect("LDAR/STLR effects");
            let atomic_effect = effects
                .iter()
                .find(|effect| matches!(effect, Effect::Aarch64AtomicAccess { .. }))
                .expect("LDAR/STLR must emit per-access atomic metadata");
            assert_effect_blocker(atomic_effect, expected_code, expected_missing_witnesses);

            let blocker = effect_proof_consumer_blocker(atomic_effect).expect("blocker metadata");
            assert!(
                blocker.scalar_data_plane_represented,
                "LDAR/STLR ordering blocker must coexist with represented scalar data effects"
            );

            match opcode {
                Opcode::Ldar => {
                    assert!(effects.iter().any(|effect| matches!(effect, Effect::MemRead { .. })));
                    assert!(effects.iter().any(|effect| matches!(effect, Effect::RegWrite { .. })));
                }
                Opcode::Stlr => {
                    assert!(effects.iter().any(|effect| matches!(effect, Effect::MemWrite { .. })));
                }
                _ => unreachable!("only LDAR/STLR cases are listed"),
            }
        }
    }

    #[test]
    fn exclusive_monitor_evidence_is_typed_and_not_available_for_ldar_stlr() {
        assert!(
            aarch64_exclusive_monitor_evidence(Opcode::Ldar).is_none(),
            "LDAR is a non-exclusive acquire access modeled by Aarch64AtomicAccess"
        );
        assert!(
            aarch64_exclusive_monitor_evidence(Opcode::Stlr).is_none(),
            "STLR is a non-exclusive release access modeled by Aarch64AtomicAccess"
        );

        let cases = [
            (
                Opcode::Ldxr,
                Aarch64AtomicAccessKind::Load,
                Aarch64ExclusiveOrdering::Relaxed,
                Aarch64ExclusiveMonitorOperation::LoadReserve,
                false,
                LDXR_MISSING_WITNESSES,
            ),
            (
                Opcode::Stxr,
                Aarch64AtomicAccessKind::Store,
                Aarch64ExclusiveOrdering::Relaxed,
                Aarch64ExclusiveMonitorOperation::StoreConditional,
                true,
                STXR_MISSING_WITNESSES,
            ),
            (
                Opcode::Ldaxr,
                Aarch64AtomicAccessKind::Load,
                Aarch64ExclusiveOrdering::Acquire,
                Aarch64ExclusiveMonitorOperation::LoadReserve,
                false,
                LDAXR_MISSING_WITNESSES,
            ),
            (
                Opcode::Stlxr,
                Aarch64AtomicAccessKind::Store,
                Aarch64ExclusiveOrdering::Release,
                Aarch64ExclusiveMonitorOperation::StoreConditional,
                true,
                STLXR_MISSING_WITNESSES,
            ),
        ];

        for (opcode, access, ordering, monitor_operation, reports_status, missing_witnesses) in
            cases
        {
            let evidence =
                aarch64_exclusive_monitor_evidence(opcode).expect("exclusive monitor evidence");
            assert_eq!(evidence.access, access, "{opcode:?}");
            assert_eq!(evidence.ordering, ordering, "{opcode:?}");
            assert_eq!(evidence.monitor_operation, monitor_operation, "{opcode:?}");
            assert_eq!(evidence.reports_status, reports_status, "{opcode:?}");
            assert_eq!(evidence.missing_witnesses, missing_witnesses, "{opcode:?}");
            assert!(
                evidence.blocker_code.starts_with("aarch64-"),
                "{opcode:?} should have machine-readable blocker code"
            );

            let detail = aarch64_atomic_unsupported_detail(opcode);
            assert!(detail.contains("fail-closed"), "{opcode:?}: {detail}");
            assert!(detail.contains("proof-consumed"), "{opcode:?}: {detail}");
            assert!(detail.contains("status=not proof-consumed"), "{opcode:?}: {detail}");
            assert!(detail.contains("blocker_code="), "{opcode:?}: {detail}");
            assert!(detail.contains("missing_witnesses="), "{opcode:?}: {detail}");
            assert!(detail.contains("monitor reservation state"), "{opcode:?}: {detail}");
            assert!(detail.contains("monitor invalidation"), "{opcode:?}: {detail}");
            assert!(detail.contains("thread identity"), "{opcode:?}: {detail}");
            for witness in missing_witnesses {
                assert!(detail.contains(witness), "{opcode:?} missing {witness}: {detail}");
            }
            if reports_status {
                assert!(
                    detail.contains("store-conditional status result"),
                    "{opcode:?} should require status witness: {detail}"
                );
            }
        }
    }

    #[test]
    fn fp_register_write_effects_remain_explicit_unconsumed_fp_simd_blockers() {
        let state = MachineState::symbolic();
        let insn = decode(0x1E62_2820); // FADD D0, D1, D2
        assert_eq!(insn.opcode, Opcode::Fadd);

        let effects = Aarch64Semantics.effects(&state, &insn).expect("FADD effects");
        let fp_write = effects
            .iter()
            .find(|effect| matches!(effect, Effect::FpRegWrite { .. }))
            .expect("FADD must keep FP state explicit");
        assert_effect_blocker(
            fp_write,
            "aarch64-fp-register-write-not-proof-consumed",
            FP_WRITE_MISSING_WITNESSES,
        );
        assert!(
            !effects.iter().any(|effect| matches!(effect, Effect::RegWrite { .. })),
            "FP writes must not silently lower to scalar GPR writes"
        );
    }

    #[test]
    fn exclusive_atomic_opcodes_fail_closed_with_diagnostics() {
        let state = MachineState::symbolic();
        let cases = [
            (0xC8_5F_7C_20, Opcode::Ldxr, "exclusive monitor"),
            (0xC8_02_7C_20, Opcode::Stxr, "conditionally stores"),
            (0xC8_5F_FC_20, Opcode::Ldaxr, "acquire memory ordering"),
            (0xC8_02_FC_20, Opcode::Stlxr, "release memory ordering"),
        ];

        for (encoding, opcode, expected_detail) in cases {
            let insn = fallthrough_insn_with_opcode(encoding, opcode);
            assert_eq!(insn.opcode, opcode);

            let err = Aarch64Semantics
                .effects(&state, &insn)
                .expect_err("atomic/exclusive instructions must fail closed");

            match err {
                SemError::UnsupportedAtomic { opcode: actual_opcode, detail } => {
                    assert_eq!(actual_opcode, opcode);
                    assert!(
                        detail.contains(expected_detail),
                        "{opcode:?} diagnostic should mention {expected_detail:?}, got {detail:?}"
                    );
                    assert!(
                        detail.contains("proof-consumed"),
                        "{opcode:?} diagnostic should block until proof consumption exists: {detail:?}"
                    );
                    assert!(
                        detail.contains("monitor reservation state")
                            && detail.contains("monitor invalidation")
                            && detail.contains("thread identity"),
                        "{opcode:?} diagnostic should name monitor/thread witnesses: {detail:?}"
                    );
                    if matches!(opcode, Opcode::Stxr | Opcode::Stlxr) {
                        assert!(
                            detail.contains("store-conditional status result"),
                            "{opcode:?} diagnostic should name missing status witness: {detail:?}"
                        );
                    }
                }
                other => panic!("expected UnsupportedAtomic for {opcode:?}, got {other:?}"),
            }
        }
    }

    #[test]
    fn aarch64_system_trap_wait_and_simd_gaps_fail_closed_with_typed_proof_blockers() {
        let state = MachineState::symbolic();
        let decoded_cases: &[(u32, Opcode, &str, &[&str])] = &[
            (
                0xD4_00_00_01,
                Opcode::Svc,
                "trap/syscall",
                &["syscall", "kernel/process state", "proof-grade"],
            ),
            (
                0xD4_00_00_62,
                Opcode::Hvc,
                "privileged trap",
                &["hypervisor", "EL2 state", "proof-grade"],
            ),
            (0xD4_00_00_83, Opcode::Smc, "privileged trap", &["secure monitor", "proof-grade"]),
            (
                0xD4_20_00_20,
                Opcode::Brk,
                "trap/debug",
                &["debug exception", "handler effects", "proof-grade"],
            ),
            (
                0xD4_40_00_C0,
                Opcode::Hlt,
                "trap/debug",
                &["halt/debug", "privileged/debug state", "proof-grade"],
            ),
            (
                0xD5_3B_42_00,
                Opcode::Mrs,
                "system register",
                &["system register state", "privilege checks", "proof-grade"],
            ),
            (
                0xD5_1B_42_00,
                Opcode::Msr,
                "system register",
                &["system register state", "side effects", "proof-grade"],
            ),
            (
                0x58_00_00_80,
                Opcode::LdrLiteral,
                "literal load",
                &["PC-relative literal-pool memory", "memory snapshot", "proof-grade"],
            ),
            (
                0xD5_03_20_5F,
                Opcode::Wfe,
                "system wait/hint",
                &["event state", "thread identity", "proof-grade"],
            ),
            (
                0xD5_03_20_7F,
                Opcode::Wfi,
                "system wait/hint",
                &["interrupt state", "thread identity", "proof-grade"],
            ),
        ];

        for (encoding, opcode, expected_category, expected_terms) in decoded_cases {
            let insn = decode(*encoding);
            assert_eq!(insn.opcode, *opcode);
            assert_typed_aarch64_proof_blocker(
                &state,
                &insn,
                *opcode,
                expected_category,
                expected_terms,
            );
        }

        let simd_insn = fallthrough_insn_with_opcode(0x0E20_1C00, Opcode::SimdMov);
        assert_typed_aarch64_proof_blocker(
            &state,
            &simd_insn,
            Opcode::SimdMov,
            "FP/SIMD",
            &["vector/FP architectural state", "lane layout", "proof-grade"],
        );
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Aarch64OpcodeCoverage {
        Modeled,
        TypedProofBlocker,
        GenericFallback,
    }

    #[test]
    fn aarch64_opcode_category_coverage_audit_has_no_generic_known_gaps() {
        let modeled: &[Opcode] = &[
            Opcode::Add,
            Opcode::Adds,
            Opcode::Sub,
            Opcode::Subs,
            Opcode::Adc,
            Opcode::Adcs,
            Opcode::Sbc,
            Opcode::Sbcs,
            Opcode::Madd,
            Opcode::Msub,
            Opcode::Smaddl,
            Opcode::Umaddl,
            Opcode::Smsubl,
            Opcode::Umsubl,
            Opcode::Smulh,
            Opcode::Umulh,
            Opcode::Udiv,
            Opcode::Sdiv,
            Opcode::And,
            Opcode::Ands,
            Opcode::Orr,
            Opcode::Eor,
            Opcode::Bic,
            Opcode::Bics,
            Opcode::Orn,
            Opcode::Eon,
            Opcode::Movz,
            Opcode::Movn,
            Opcode::Movk,
            Opcode::Lslv,
            Opcode::Lsrv,
            Opcode::Asrv,
            Opcode::Rorv,
            Opcode::Ubfm,
            Opcode::Sbfm,
            Opcode::Bfm,
            Opcode::Extr,
            Opcode::Clz,
            Opcode::Rbit,
            Opcode::Rev,
            Opcode::Rev16,
            Opcode::Rev32,
            Opcode::Cls,
            Opcode::Csel,
            Opcode::Csinc,
            Opcode::Csinv,
            Opcode::Csneg,
            Opcode::Ccmp,
            Opcode::Ccmn,
            Opcode::Adr,
            Opcode::Adrp,
            Opcode::Ldr,
            Opcode::Ldrb,
            Opcode::Ldrh,
            Opcode::Ldrsb,
            Opcode::Ldrsh,
            Opcode::Ldrsw,
            Opcode::Ldp,
            Opcode::Str,
            Opcode::Strb,
            Opcode::Strh,
            Opcode::Stp,
            Opcode::Ldar,
            Opcode::Stlr,
            Opcode::B,
            Opcode::Bl,
            Opcode::Br,
            Opcode::Blr,
            Opcode::Ret,
            Opcode::BCond,
            Opcode::Cbz,
            Opcode::Cbnz,
            Opcode::Tbz,
            Opcode::Tbnz,
            Opcode::Nop,
            Opcode::Yield,
            Opcode::Sev,
            Opcode::Sevl,
            Opcode::Prfm,
            Opcode::Dmb,
            Opcode::Dsb,
            Opcode::Isb,
            Opcode::Clrex,
            Opcode::Fadd,
            Opcode::Fsub,
            Opcode::Fmul,
            Opcode::Fdiv,
            Opcode::Fcmp,
            Opcode::FmovReg,
            Opcode::FmovImm,
            Opcode::Fneg,
            Opcode::Fabs,
            Opcode::Fsqrt,
            Opcode::Fcvtzs,
            Opcode::Fcvtzu,
            Opcode::Scvtf,
            Opcode::Ucvtf,
            Opcode::Fcvt,
            Opcode::Fcsel,
        ];
        let typed_blockers: &[Opcode] = &[
            Opcode::Ldxr,
            Opcode::Stxr,
            Opcode::Ldaxr,
            Opcode::Stlxr,
            Opcode::LdrLiteral,
            Opcode::Svc,
            Opcode::Hvc,
            Opcode::Smc,
            Opcode::Brk,
            Opcode::Hlt,
            Opcode::Mrs,
            Opcode::Msr,
            Opcode::Wfe,
            Opcode::Wfi,
            Opcode::SimdMov,
        ];
        let generic_fallbacks: &[Opcode] = &[Opcode::Mov, Opcode::Syscall, Opcode::Unknown];

        for opcode in modeled {
            assert_eq!(
                observed_aarch64_coverage(*opcode),
                Aarch64OpcodeCoverage::Modeled,
                "{opcode:?} should route to modeled AArch64 semantics or operand validation"
            );
        }
        for opcode in typed_blockers {
            assert_eq!(
                observed_aarch64_coverage(*opcode),
                Aarch64OpcodeCoverage::TypedProofBlocker,
                "{opcode:?} should fail closed with a typed proof blocker"
            );
        }
        for opcode in generic_fallbacks {
            assert_eq!(
                observed_aarch64_coverage(*opcode),
                Aarch64OpcodeCoverage::GenericFallback,
                "{opcode:?} is outside the known AArch64 semantic surface"
            );
        }
    }

    fn observed_aarch64_coverage(opcode: Opcode) -> Aarch64OpcodeCoverage {
        let state = MachineState::symbolic();
        let insn = fallthrough_insn_with_opcode(0xD503_201F, opcode);
        match Aarch64Semantics.effects(&state, &insn) {
            Err(SemError::UnsupportedOpcode(_)) => Aarch64OpcodeCoverage::GenericFallback,
            Err(SemError::UnsupportedAtomic { .. })
            | Err(SemError::UnsupportedAarch64ProofBlocker { .. }) => {
                Aarch64OpcodeCoverage::TypedProofBlocker
            }
            Ok(_) | Err(SemError::InvalidOperand { .. }) | Err(SemError::WidthMismatch { .. }) => {
                Aarch64OpcodeCoverage::Modeled
            }
        }
    }

    fn assert_typed_aarch64_proof_blocker(
        state: &MachineState,
        insn: &Instruction,
        expected_opcode: Opcode,
        expected_category: &str,
        expected_terms: &[&str],
    ) {
        let err = Aarch64Semantics
            .effects(state, insn)
            .expect_err("unsupported AArch64 proof gap must fail closed");

        match err {
            SemError::UnsupportedAarch64ProofBlocker { opcode, category, detail } => {
                let evidence = aarch64_opcode_proof_blocker_evidence(expected_opcode);
                assert_eq!(opcode, expected_opcode);
                assert_eq!(category, expected_category);
                assert_eq!(category, evidence.category);
                assert!(
                    detail.contains("fail-closed"),
                    "{expected_opcode:?} diagnostic should be fail-closed: {detail}"
                );
                assert!(
                    detail.contains(&format!("blocker_code={}", evidence.blocker_code)),
                    "{expected_opcode:?} diagnostic should carry blocker code: {detail}"
                );
                assert!(
                    detail.contains("status=not proof-consumed"),
                    "{expected_opcode:?} diagnostic should name proof-consumption status: {detail}"
                );
                assert!(
                    detail.contains("missing_witnesses="),
                    "{expected_opcode:?} diagnostic should carry missing witness metadata: {detail}"
                );
                for expected in expected_terms {
                    assert!(
                        detail.contains(expected),
                        "{expected_opcode:?} diagnostic should mention {expected:?}: {detail}"
                    );
                }
                for witness in evidence.missing_witnesses {
                    assert!(
                        detail.contains(witness),
                        "{expected_opcode:?} diagnostic should mention witness {witness:?}: {detail}"
                    );
                }
            }
            SemError::UnsupportedOpcode(opcode) => {
                panic!(
                    "expected typed AArch64 proof blocker for {expected_opcode:?}, got generic UnsupportedOpcode({opcode:?})"
                );
            }
            other => panic!(
                "expected typed AArch64 proof blocker for {expected_opcode:?}, got {other:?}"
            ),
        }
    }
}
