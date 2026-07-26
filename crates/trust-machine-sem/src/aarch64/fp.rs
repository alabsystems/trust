// trust-machine-sem: AArch64 FP/SIMD instruction semantics
//
// FADD/FSUB/FMUL/FDIV (f32 AND f64) are modeled to BIT-EXACT IEEE-754 semantics
// via the FP `Formula` nodes (`FpFromBits`/`FpAdd|FpSub|FpMul|FpDiv(RNE)`/
// `FpToIeeeBv`): the BV-typed register lanes are reinterpreted as the format's
// float (f64 = D-lane, eb 11 / sb 53; f32 = S-lane, eb 8 / sb 24), combined
// under round-to-nearest-even, and reinterpreted back to their `eb+sb`-bit
// pattern. See `sem_fadd`/`sem_fsub`/`sem_fmul`/`sem_fdiv`, `fp_binop_bits`, and
// `FpFormat`.
//
// The FpFromBits/FpToIeeeBv reinterprets and the fp.* ops are width-PARAMETRIC
// (the ay bridge extracts sign/exp/sig fields from `eb`/`sb`), so f32 rides the
// IDENTICAL shape as f64 at (eb=8, sb=24) with no soundness gap — the residual
// `B-aarch64-fp-pending` only ever covered f32 FCVT (BvToFP/FPToFP/FPToSBv
// conversions) and FMA, NOT f32 add/sub/mul/div.
//
// FDIV needs NO guard: IEEE-754 division by zero yields ±inf (or NaN for 0/0),
// NOT a trap, so the `FpDiv(RNE, ..)` model is sound unconditionally.
//
// The REMAINING scalar FP ops (FNEG/FABS/FSQRT/FCMP/conversions) are still
// modeled as bitvector approximations — an over-approximation sufficient for
// control-flow/memory dataflow but NOT precise FP value reasoning. FADD/FSUB/
// FMUL/FDIV at f16 fail closed (only f32/f64 are wired).
//
// Limitation: replace the remaining BvSDiv/etc. approximations for the OTHER
// ops with the FpNeg/FpSqrt/… shapes for bit-exact semantics; not yet done.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_disasm::Instruction;
use trust_disasm::operand::{Operand, RegKind};
use trust_types::{Formula, RoundingMode};

use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

use super::{Aarch64Semantics, condition_to_formula, extract_condition, pc_advance};

impl Aarch64Semantics {
    // -------------------------------------------------------------------
    // Scalar FP arithmetic: FADD, FSUB, FMUL, FDIV
    // -------------------------------------------------------------------

    /// FADD: Fd = Fn + Fm — BIT-EXACT IEEE-754 addition (F32 and F64).
    ///
    /// SOUNDNESS. The V registers are BV-typed (128-bit); a scalar `FADD` reads
    /// the low `width`-bit lane of each source (`read_fpr(_, width)` =
    /// `V_[width-1:0]`; D-lane for f64/width 64, S-lane for f32/width 32) as a raw
    /// bit pattern. We REINTERPRET both lanes as the format's float
    /// (`FpFromBits`, BV->FP — eb 11 / sb 53 for f64, eb 8 / sb 24 for f32), add
    /// them under round-to-nearest-even (`FpAdd(RNE, ..)` — the AArch64 default
    /// rounding mode, which is what native Rust `f32/f64 +` compiles to), then
    /// REINTERPRET the result BACK to its `width`-bit IEEE pattern (`FpToIeeeBv`,
    /// FP->BV) so it lands in the BV-typed register file. This models the HARDWARE
    /// fp.add exactly: the round-trip
    /// `FpToIeeeBv(FpAdd(RNE, FpFromBits(a), FpFromBits(b)))` is bit-preserving,
    /// so NaN payloads and the sign of ±0.0 are carried through verbatim — a
    /// structural `Eq` over these BVs is bit-exact (unlike `fp.eq`).
    ///
    /// FAIL-CLOSED on F16: only the F32 (S-lane, width 32) and F64 (D-lane, width
    /// 64) lowerings are modeled to bit-exact IEEE semantics here. A half FADD
    /// returns `Unsupported` rather than a wrong-width or approximate result.
    pub(super) fn sem_fadd(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_arith(state, insn, "FADD", |fmt, a, b| fmt.add_bits(a, b))
    }

    /// FSUB: Fd = Fn - Fm — BIT-EXACT IEEE-754 subtraction (F32 and F64).
    ///
    /// SOUNDNESS. Identical two-sided FP shape as [`sem_fadd`]: reinterpret the
    /// low `width`-bit lanes of each source as the format's float (`FpFromBits`,
    /// BV->FP), subtract under round-to-nearest-even (`FpSub(RNE, ..)`, the
    /// AArch64 default which native Rust `-` compiles to), then reinterpret the
    /// result BACK to its `width`-bit IEEE pattern (`FpToIeeeBv`, FP->BV).
    /// Bit-preserving: NaN payloads and the sign of ±0.0 survive verbatim, so a
    /// structural `Eq` against the IR-semantics side is bit-exact.
    ///
    /// FAIL-CLOSED on F16: only F32 (width 32) and F64 (width 64) are modeled.
    pub(super) fn sem_fsub(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_arith(state, insn, "FSUB", |fmt, a, b| fmt.sub_bits(a, b))
    }

    /// FMUL: Fd = Fn * Fm — BIT-EXACT IEEE-754 multiplication (F32 and F64).
    ///
    /// SOUNDNESS. Identical two-sided FP shape as [`sem_fadd`]: reinterpret the
    /// low `width`-bit lanes as the format's float (`FpFromBits`), multiply under
    /// round-to-nearest-even (`FpMul(RNE, ..)`, the AArch64 default which native
    /// Rust `*` compiles to), then reinterpret BACK to the `width`-bit IEEE
    /// pattern (`FpToIeeeBv`). Bit-preserving; a structural `Eq` against the
    /// IR-semantics side is bit-exact.
    ///
    /// FAIL-CLOSED on F16: only F32 (width 32) and F64 (width 64) are modeled.
    pub(super) fn sem_fmul(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_arith(state, insn, "FMUL", |fmt, a, b| fmt.mul_bits(a, b))
    }

    /// FDIV: Fd = Fn / Fm — BIT-EXACT IEEE-754 division (F32 and F64).
    ///
    /// SOUNDNESS. Identical two-sided FP shape as [`sem_fadd`]: reinterpret the
    /// low `width`-bit lanes as the format's float (`FpFromBits`), divide under
    /// round-to-nearest-even (`FpDiv(RNE, ..)`, the AArch64 default which native
    /// Rust `/` compiles to), then reinterpret BACK to the `width`-bit IEEE
    /// pattern (`FpToIeeeBv`). Bit-preserving; a structural `Eq` against the
    /// IR-semantics side is bit-exact.
    ///
    /// NO GUARD. IEEE-754 division is TOTAL: `x / 0.0` yields ±inf (sign of the
    /// result following the usual sign rule) and `0.0 / 0.0` yields NaN — NEITHER
    /// traps. So modeling FDIV unconditionally as `FpDiv(RNE, ..)` is sound; no
    /// divisor-nonzero precondition is needed (unlike integer SDIV/UDIV, which DO
    /// trap on a zero divisor).
    ///
    /// FAIL-CLOSED on F16: only F32 (width 32) and F64 (width 64) are modeled.
    pub(super) fn sem_fdiv(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_arith(state, insn, "FDIV", |fmt, a, b| fmt.div_bits(a, b))
    }

    /// Shared bit-exact FP arithmetic driver for FADD/FSUB/FMUL/FDIV at F32 and
    /// F64. Resolves the IEEE format from the destination lane width
    /// ([`FpFormat::for_width`]; fail-closed on any width other than 32/64), reads
    /// the two source lanes, applies `build` (which emits the two-sided
    /// `FpToIeeeBv(Fp*(RNE, FpFromBits, FpFromBits))` shape at the format's
    /// eb/sb), and writes the `width`-bit result. Writing the S/D lane
    /// zero-clears the upper bits of V (modeled by the `FpRegWrite` effect's
    /// widen-to-128 in `MachineState::apply_effect`). FAIL-CLOSED on f16.
    fn sem_fp_arith(
        &self,
        state: &MachineState,
        insn: &Instruction,
        opname: &'static str,
        build: impl FnOnce(FpFormat, Formula, Formula) -> Formula,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fmt = FpFormat::for_width(width).ok_or_else(|| {
            SemError::UnsupportedAarch64ProofBlocker {
                opcode: insn.opcode,
                category: "fp-scalar-width",
                detail: format!(
                    "{opname} is only modeled to bit-exact IEEE-754 semantics for f32 \
                     (S-lane, width 32) and f64 (D-lane, width 64); width {width} \
                     (f16) unsupported"
                ),
            }
        })?;
        let fn_bv = read_fp_operand(state, insn, 1, width)?;
        let fm_bv = read_fp_operand(state, insn, 2, width)?;
        let result = build(fmt, fn_bv, fm_bv);
        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP compare: FCMP
    // -------------------------------------------------------------------

    /// FCMP: compare Fn and Fm (or Fn and 0.0), set NZCV.
    ///
    /// AArch64 FCMP flag semantics (IEEE 754 comparison):
    /// - Equal:       NZCV = 0110
    /// - Less than:   NZCV = 1000
    /// - Greater than: NZCV = 0010
    /// - Unordered:   NZCV = 0011 (NaN)
    ///
    /// We model this as a bitvector signed comparison (approximation).
    pub(super) fn sem_fcmp(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (rn_idx, width) = extract_fp_reg(insn, 0)?;
        let fn_val = state.read_fpr(rn_idx, width);

        let fm_val = match insn.operand(1) {
            Some(Operand::Imm(0)) => Formula::BitVec { value: 0, width },
            Some(Operand::Reg(r)) if r.kind == RegKind::Simd => {
                state.read_fpr(r.index, u32::from(r.width))
            }
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected FP register or zero".into(),
                });
            }
        };

        // Model as signed comparison for approximation.
        let is_equal = Formula::Eq(Box::new(fn_val.clone()), Box::new(fm_val.clone()));
        let is_less = Formula::BvSLt(Box::new(fn_val.clone()), Box::new(fm_val.clone()), width);

        // N = 1 if fn < fm (less than)
        let n = is_less.clone();
        // Z = 1 if fn == fm (equal)
        let z = is_equal.clone();
        // C = 1 if fn >= fm (greater or equal) — i.e., NOT less than
        let c = Formula::Not(Box::new(is_less));
        // V = 0 (we cannot model NaN/unordered with bitvectors)
        let v = Formula::Bool(false);

        let mut effects = vec![Effect::FlagUpdate { n, z, c, v }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP move: FMOV (register and immediate)
    // -------------------------------------------------------------------

    /// FMOV (register): Fd = Fn, or GPR<->FP transfer.
    pub(super) fn sem_fmov_reg(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);

        // Read source value.
        let src_val = match src.kind {
            RegKind::Simd => state.read_fpr(src.index, src_width),
            RegKind::Gpr => state.read_gpr(src.index, src_width),
            RegKind::Zr => Formula::BitVec { value: 0, width: src_width },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: format!("unexpected register kind: {:?}", src.kind),
                });
            }
        };

        // Match widths if needed (truncate or zero-extend for bit transfer).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        // Write to destination.
        let effect = match dst.kind {
            RegKind::Simd => Effect::FpRegWrite { index: dst.index, width: dst_width, value },
            RegKind::Gpr => Effect::RegWrite { index: dst.index, width: dst_width, value },
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: format!("unexpected destination kind: {:?}", dst.kind),
                });
            }
        };

        Ok(vec![effect, pc_advance(state, insn)])
    }

    /// FMOV (immediate): Fd = imm8 (expanded to FP constant).
    ///
    /// The 8-bit immediate encodes an FP constant per AArch64 spec.
    /// We store the raw imm8 as a bitvector for now.
    pub(super) fn sem_fmov_imm(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;

        let imm8 = match insn.operand(1) {
            Some(Operand::Imm(v)) => *v,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected immediate".into(),
                });
            }
        };

        // Expand imm8 to FP constant per AArch64 spec.
        let value = expand_fp_imm8(imm8, width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP unary: FNEG, FABS, FSQRT
    // -------------------------------------------------------------------

    /// FNEG: Fd = -Fn. Modeled as two's complement negation (BvSub(0, Fn)).
    pub(super) fn sem_fneg(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // FP negate: flip sign bit. For IEEE 754, this is XOR with sign-bit mask.
        let sign_mask = Formula::BvShl(
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let result = Formula::BvXor(Box::new(fn_val), Box::new(sign_mask), width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FABS: Fd = |Fn|. Clear the sign bit.
    pub(super) fn sem_fabs(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // Clear sign bit: AND with ~(1 << (width-1)).
        let sign_mask = Formula::BvShl(
            Box::new(Formula::BitVec { value: 1, width }),
            Box::new(Formula::BitVec { value: i128::from(width - 1), width }),
            width,
        );
        let inv_mask = Formula::BvNot(Box::new(sign_mask), width);
        let result = Formula::BvAnd(Box::new(fn_val), Box::new(inv_mask), width);

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FSQRT: Fd = sqrt(Fn). No bitvector equivalent -- model as identity
    /// (the value passes through unchanged). This is an over-approximation
    /// that preserves dataflow without modeling the actual square root.
    pub(super) fn sem_fsqrt(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;

        // Over-approximation: Fd = Fn (preserves dataflow).
        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: fn_val }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP conversion: FCVTZS, FCVTZU, SCVTF, UCVTF, FCVT
    // -------------------------------------------------------------------

    /// FCVTZS: Convert FP to signed integer, rounding toward zero.
    /// Modeled as bitvector extraction/sign-extension from FP width to int width.
    pub(super) fn sem_fcvtzs(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_to_int(state, insn, true)
    }

    /// FCVTZU: Convert FP to unsigned integer, rounding toward zero.
    pub(super) fn sem_fcvtzu(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_fp_to_int(state, insn, false)
    }

    /// Shared FP-to-int conversion.
    fn sem_fp_to_int(
        &self,
        state: &MachineState,
        insn: &Instruction,
        _signed: bool,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);
        let src_val = state.read_fpr(src.index, src_width);

        // Model FP-to-int as bitvector reinterpretation (truncate or extend).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::RegWrite { index: dst.index, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// SCVTF: Convert signed integer to FP.
    pub(super) fn sem_scvtf(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_int_to_fp(state, insn)
    }

    /// UCVTF: Convert unsigned integer to FP.
    pub(super) fn sem_ucvtf(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_int_to_fp(state, insn)
    }

    /// Shared int-to-FP conversion.
    fn sem_int_to_fp(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let dst = match insn.operand(0) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 0,
                    detail: "expected register".into(),
                });
            }
        };
        let src = match insn.operand(1) {
            Some(Operand::Reg(r)) => r,
            _ => {
                return Err(SemError::InvalidOperand {
                    opcode: insn.opcode,
                    index: 1,
                    detail: "expected register".into(),
                });
            }
        };

        let dst_width = u32::from(dst.width);
        let src_width = u32::from(src.width);
        let src_val = state.read_gpr(src.index, src_width);

        // Model int-to-FP as bitvector reinterpretation (truncate or extend).
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::FpRegWrite { index: dst.index, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    /// FCVT: Convert between FP precisions (e.g., S->D, D->S).
    pub(super) fn sem_fcvt(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, dst_width) = extract_fp_dst(insn)?;
        let (src_idx, src_width) = extract_fp_reg(insn, 1)?;
        let src_val = state.read_fpr(src_idx, src_width);

        // Width conversion: truncate or zero-extend.
        let value = if src_width == dst_width {
            src_val
        } else if src_width > dst_width {
            Formula::BvExtract { inner: Box::new(src_val), high: dst_width - 1, low: 0 }
        } else {
            Formula::BvZeroExt(Box::new(src_val), dst_width)
        };

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width: dst_width, value }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }

    // -------------------------------------------------------------------
    // FP conditional select: FCSEL
    // -------------------------------------------------------------------

    /// FCSEL: Fd = cond ? Fn : Fm.
    pub(super) fn sem_fcsel(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;
        let fm_val = read_fp_operand(state, insn, 2, width)?;
        let cond = extract_condition(insn, 3)?;
        let cond_formula = condition_to_formula(state, cond);

        let result = Formula::Ite(Box::new(cond_formula), Box::new(fn_val), Box::new(fm_val));

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
        effects.push(pc_advance(state, insn));
        Ok(effects)
    }
}

// ---------------------------------------------------------------------------
// FP helper functions
// ---------------------------------------------------------------------------

/// An IEEE-754 binary interchange format resolved from a scalar FP lane width.
///
/// The two AArch64 scalar formats this module models to bit-exact semantics:
///   * `F32` — S-lane (width 32): 8 exponent bits, 24 significand bits
///     (23 stored + 1 hidden). `eb + sb == 32`.
///   * `F64` — D-lane (width 64): 11 exponent bits, 53 significand bits
///     (52 stored + 1 hidden). `eb + sb == 64`.
///
/// f16 is intentionally ABSENT: it fails closed at [`FpFormat::for_width`].
#[derive(Clone, Copy, Debug)]
pub(super) enum FpFormat {
    F32,
    F64,
}

impl FpFormat {
    /// Resolve the IEEE format for a scalar FP lane `width`, or `None` (=>
    /// fail-closed) for any width other than 32 (f32) or 64 (f64).
    fn for_width(width: u32) -> Option<Self> {
        match width {
            32 => Some(FpFormat::F32),
            64 => Some(FpFormat::F64),
            _ => None,
        }
    }

    /// `(eb, sb)` — exponent-bit and significand-bit counts (`eb + sb == width`).
    fn eb_sb(self) -> (u32, u32) {
        match self {
            // f32: 1 sign + 8 exp + 23 stored-significand; sb includes the hidden bit.
            FpFormat::F32 => (8, 24),
            // f64: 1 sign + 11 exp + 52 stored-significand; sb includes the hidden bit.
            FpFormat::F64 => (11, 53),
        }
    }

    /// Bit-exact FP addition over two `width`-bit IEEE bit patterns:
    /// `FpToIeeeBv(FpAdd(RNE, FpFromBits(a), FpFromBits(b)))` at this format's
    /// eb/sb. Same two-sided, bit-preserving shape the IR-semantics side emits
    /// (`verify_output::fp_add_bits`), so a structural `Eq` discharges UNSAT.
    fn add_bits(self, a_bits: Formula, b_bits: Formula) -> Formula {
        self.binop_bits(a_bits, b_bits, |rm, a, b| Formula::FpAdd(rm, a, b))
    }

    /// Bit-exact FP subtraction: `FpToIeeeBv(FpSub(RNE, FpFromBits(a), ..))`.
    fn sub_bits(self, a_bits: Formula, b_bits: Formula) -> Formula {
        self.binop_bits(a_bits, b_bits, |rm, a, b| Formula::FpSub(rm, a, b))
    }

    /// Bit-exact FP multiplication: `FpToIeeeBv(FpMul(RNE, FpFromBits(a), ..))`.
    fn mul_bits(self, a_bits: Formula, b_bits: Formula) -> Formula {
        self.binop_bits(a_bits, b_bits, |rm, a, b| Formula::FpMul(rm, a, b))
    }

    /// Bit-exact FP division: `FpToIeeeBv(FpDiv(RNE, FpFromBits(a), ..))`. NO
    /// GUARD: IEEE-754 division is total (`x/0.0` = ±inf, `0.0/0.0` = NaN —
    /// neither traps), so the unconditional `FpDiv(RNE, ..)` model is sound.
    fn div_bits(self, a_bits: Formula, b_bits: Formula) -> Formula {
        self.binop_bits(a_bits, b_bits, |rm, a, b| Formula::FpDiv(rm, a, b))
    }

    /// Shared two-sided FP-round-trip constructor. REINTERPRET each `width`-bit
    /// lane as the format's float (`FpFromBits`, BV->FP, at this eb/sb), apply the
    /// FP op under round-to-nearest-even (`fp`, the AArch64 default), and
    /// REINTERPRET the result BACK to its `width`-bit IEEE pattern (`FpToIeeeBv`,
    /// FP->BV). The round-trip is bit-preserving.
    fn binop_bits(
        self,
        a_bits: Formula,
        b_bits: Formula,
        fp: impl FnOnce(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
    ) -> Formula {
        let (eb, sb) = self.eb_sb();
        let a_fp = Formula::FpFromBits { bits: Box::new(a_bits), eb, sb };
        let b_fp = Formula::FpFromBits { bits: Box::new(b_bits), eb, sb };
        let out = fp(
            Box::new(Formula::FpRoundingMode(RoundingMode::RNE)),
            Box::new(a_fp),
            Box::new(b_fp),
        );
        Formula::FpToIeeeBv(Box::new(out))
    }
}

/// Extract FP destination register index and width from operand 0.
fn extract_fp_dst(insn: &Instruction) -> Result<(u8, u32), SemError> {
    match insn.operand(0) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok((r.index, u32::from(r.width))),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index: 0,
            detail: "expected SIMD/FP register destination".into(),
        }),
    }
}

/// Extract FP register index and width from a given operand position.
fn extract_fp_reg(insn: &Instruction, index: usize) -> Result<(u8, u32), SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok((r.index, u32::from(r.width))),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected SIMD/FP register".into(),
        }),
    }
}

/// Read an FP operand (register) from the instruction at the given position.
fn read_fp_operand(
    state: &MachineState,
    insn: &Instruction,
    index: usize,
    width: u32,
) -> Result<Formula, SemError> {
    match insn.operand(index) {
        Some(Operand::Reg(r)) if r.kind == RegKind::Simd => Ok(state.read_fpr(r.index, width)),
        _ => Err(SemError::InvalidOperand {
            opcode: insn.opcode,
            index,
            detail: "expected SIMD/FP register operand".into(),
        }),
    }
}

/// Expand an 8-bit FP immediate to a full-width FP constant.
///
/// AArch64 FMOV immediate encoding: imm8 = abcdefgh
///   Single (32-bit): aBbb_bbbc_defg_h000_0000_0000_0000_0000 (where B = NOT b)
///   Double (64-bit): aBbb_bbbb_bbcd_efgh_0...0 (where B = NOT b)
fn expand_fp_imm8(imm8: u64, width: u32) -> Formula {
    let value = if width == 32 {
        let a = (imm8 >> 7) & 1;
        let b = (imm8 >> 6) & 1;
        let c = (imm8 >> 5) & 1;
        let d = (imm8 >> 4) & 1;
        let e = (imm8 >> 3) & 1;
        let f = (imm8 >> 2) & 1;
        let g = (imm8 >> 1) & 1;
        let h = imm8 & 1;

        let sign = a << 31;
        let exp_high = (!b & 1) << 30;
        let exp_mid = if b == 1 { 0x1F << 25 } else { 0 };
        let exp_low = c << 25;
        let mantissa = (d << 22) | (e << 21) | (f << 20) | (g << 19) | (h << 18);

        (sign | exp_high | exp_mid | exp_low | mantissa) as i128
    } else if width == 64 {
        let a = (imm8 >> 7) & 1;
        let b = (imm8 >> 6) & 1;
        let c = (imm8 >> 5) & 1;
        let d = (imm8 >> 4) & 1;
        let e = (imm8 >> 3) & 1;
        let f = (imm8 >> 2) & 1;
        let g = (imm8 >> 1) & 1;
        let h = imm8 & 1;

        let sign = a << 63;
        let exp_high = (!b & 1) << 62;
        let exp_mid = if b == 1 { 0xFFu64 << 54 } else { 0 };
        let exp_low = c << 54;
        let mantissa = (d << 51) | (e << 50) | (f << 49) | (g << 48) | (h << 47);

        (sign | exp_high | exp_mid | exp_low | mantissa) as i128
    } else {
        // For 16-bit half-precision, store raw imm8 as approximation.
        imm8 as i128
    };

    Formula::BitVec { value, width }
}

#[cfg(test)]
mod fp_format_tests {
    use super::FpFormat;
    use trust_types::Formula;

    #[test]
    fn for_width_maps_f32_and_f64_and_rejects_f16() {
        // f32 => S-lane, eb 8 / sb 24 (eb + sb == 32).
        let f32 = FpFormat::for_width(32).expect("f32 must resolve");
        assert_eq!(f32.eb_sb(), (8, 24));
        // f64 => D-lane, eb 11 / sb 53 (eb + sb == 64).
        let f64 = FpFormat::for_width(64).expect("f64 must resolve");
        assert_eq!(f64.eb_sb(), (11, 53));
        // f16 (width 16) is fail-closed at the semantics layer (None).
        assert!(FpFormat::for_width(16).is_none(), "f16 must fail closed");
        // Other odd widths also fail closed.
        assert!(FpFormat::for_width(128).is_none());
        assert!(FpFormat::for_width(80).is_none());
    }

    #[test]
    fn f32_add_bits_emits_ieee_shape_at_eb8_sb24() {
        // The width-parametric constructor emits the SAME two-sided shape as f64,
        // just at eb=8/sb=24: FpToIeeeBv(FpAdd(RNE, FpFromBits(_,8,24), _)).
        let a = Formula::Var("a".into(), trust_types::Sort::BitVec(32));
        let b_ = Formula::Var("b".into(), trust_types::Sort::BitVec(32));
        let out = FpFormat::F32.add_bits(a, b_);
        match out {
            Formula::FpToIeeeBv(inner) => match *inner {
                Formula::FpAdd(_, l, r) => {
                    assert!(matches!(*l, Formula::FpFromBits { eb: 8, sb: 24, .. }));
                    assert!(matches!(*r, Formula::FpFromBits { eb: 8, sb: 24, .. }));
                }
                other => panic!("expected FpAdd, got {other:?}"),
            },
            other => panic!("expected FpToIeeeBv, got {other:?}"),
        }
    }
}
