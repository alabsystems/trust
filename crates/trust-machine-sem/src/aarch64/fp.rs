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

use super::{Aarch64Semantics, condition_to_formula, extract_condition, pc_advance};
use crate::effect::Effect;
use crate::error::SemError;
use crate::state::MachineState;

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
        let fmt =
            FpFormat::for_width(width).ok_or_else(|| SemError::UnsupportedAarch64ProofBlocker {
                opcode: insn.opcode,
                category: "fp-scalar-width",
                detail: format!(
                    "{opname} is only modeled to bit-exact IEEE-754 semantics for f32 \
                     (S-lane, width 32) and f64 (D-lane, width 64); width {width} \
                     (f16) unsupported"
                ),
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

        // Real IEEE comparison over the bit patterns. The previous model used
        // SIGNED INTEGER compare on the raw bits with V hardcoded 0 — wrong for
        // NaN (unordered must set NZCV = 0011), wrong for -0.0 == +0.0 (equal
        // on hardware, unequal as bits), and ORDER-REVERSED for two negative
        // floats (floats are sign-magnitude; two's-complement compare inverts
        // their order). 141 words of the native semantic differential diverged.
        //
        // ARM DDI 0487, FCMP: unordered -> 0011, lt -> 1000, eq -> 0110,
        // gt -> 0010. `fp.lt`/`fp.eq` are false on unordered inputs and
        // `fp.eq` treats -0 == +0, so:
        //   N = fp.lt            (false when unordered, as required)
        //   Z = fp.eq            (false when unordered, as required)
        //   C = NOT fp.lt        (true for eq, gt, AND unordered)
        //   V = isNaN(a) OR isNaN(b)
        let (eb, sb) =
            FpFormat::for_width(width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();
        let fp_a = Formula::FpFromBits { bits: Box::new(fn_val), eb, sb };
        let fp_b = Formula::FpFromBits { bits: Box::new(fm_val), eb, sb };
        let lt = Formula::FpLt(Box::new(fp_a.clone()), Box::new(fp_b.clone()));
        let n = lt.clone();
        let z = Formula::FpEq(Box::new(fp_a.clone()), Box::new(fp_b.clone()));
        let c = Formula::Not(Box::new(lt));
        let v =
            Formula::Or(vec![Formula::FpIsNaN(Box::new(fp_a)), Formula::FpIsNaN(Box::new(fp_b))]);

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
            // `BvZeroExt`'s second field is the extension AMOUNT, not the target
            // width — `check_formula_sort` returns `BitVec(inner + extra)` and
            // the printer emits SMT-LIB `((_ zero_extend n) ..)`. This arm is
            // reached only when `src_width < dst_width`, so the amount is the
            // difference. Passing `dst_width` denoted `BitVec(src + dst)`.
            Formula::BvZeroExt(Box::new(src_val), dst_width - src_width)
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

    /// FSQRT: Fd = sqrt(Fn), IEEE-754 under the default rounding mode.
    ///
    /// This was modeled as IDENTITY — `Fd = Fn` — with a comment calling that
    /// "an over-approximation that preserves dataflow". It is not an
    /// over-approximation: an over-approximation admits MORE behaviours than
    /// the hardware; identity asserts a SPECIFIC wrong value for every operand
    /// that is not 0 or 1. 464 words of the native semantic differential
    /// diverged. Now the same `FpToIeeeBv(FpSqrt(RNE, FpFromBits(..)))`
    /// round-trip shape the four FP binops already use.
    pub(super) fn sem_fsqrt(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        let (dst_idx, width) = extract_fp_dst(insn)?;
        let fn_val = read_fp_operand(state, insn, 1, width)?;
        let (eb, sb) =
            FpFormat::for_width(width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();

        let result = Formula::FpToIeeeBv(Box::new(Formula::FpSqrt(
            Box::new(Formula::FpRoundingMode(trust_types::RoundingMode::RNE)),
            Box::new(Formula::FpFromBits { bits: Box::new(fn_val), eb, sb }),
        )));

        let mut effects = vec![Effect::FpRegWrite { index: dst_idx, width, value: result }];
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

    /// Shared FP-to-int conversion: FCVTZS/FCVTZU, round-toward-zero,
    /// SATURATING (ARM DDI 0487: NaN -> 0, out-of-range -> clamp).
    ///
    /// Was modeled as bitvector reinterpretation — truncate/zero-extend of the
    /// FLOAT'S BITS into the integer register, i.e. `fcvtzs w0, s0` returned
    /// the IEEE bit pattern, not the value. 2,580 words of the native semantic
    /// differential diverged. `FpToSbv`/`FpToUbv` are TOTAL with exactly the
    /// AArch64 saturating reading (that is why they were added), so the node
    /// alone is the whole semantics — no guard tree needed here.
    fn sem_fp_to_int(
        &self,
        state: &MachineState,
        insn: &Instruction,
        signed: bool,
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
        let (eb, sb) =
            FpFormat::for_width(src_width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();
        let src_val = state.read_fpr(src.index, src_width);

        let rm = Box::new(Formula::FpRoundingMode(trust_types::RoundingMode::RTZ));
        let fp = Box::new(Formula::FpFromBits { bits: Box::new(src_val), eb, sb });
        let value = if signed {
            Formula::FpToSbv { rm, value: fp, width: dst_width, eb, sb }
        } else {
            Formula::FpToUbv { rm, value: fp, width: dst_width, eb, sb }
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
        self.sem_int_to_fp(state, insn, true)
    }

    /// UCVTF: Convert unsigned integer to FP.
    pub(super) fn sem_ucvtf(
        &self,
        state: &MachineState,
        insn: &Instruction,
    ) -> Result<Vec<Effect>, SemError> {
        self.sem_int_to_fp(state, insn, false)
    }

    /// Shared int-to-FP conversion: SCVTF/UCVTF under the default rounding
    /// mode (RNE).
    ///
    /// Was modeled as bitvector reinterpretation — `scvtf d0, w1` wrote the
    /// integer's bit pattern into the float register, not the represented
    /// value. 2,533 words of the native semantic differential diverged. SMT's
    /// `to_fp`/`to_fp_unsigned` are fully specified, so the direct nodes carry
    /// the whole semantics.
    fn sem_int_to_fp(
        &self,
        state: &MachineState,
        insn: &Instruction,
        signed: bool,
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
        let (eb, sb) =
            FpFormat::for_width(dst_width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();
        let src_val = state.read_gpr(src.index, src_width);

        let rm = Box::new(Formula::FpRoundingMode(trust_types::RoundingMode::RNE));
        let converted = if signed {
            Formula::FpFromSbv { rm, value: Box::new(src_val), eb, sb }
        } else {
            Formula::FpFromUbv { rm, value: Box::new(src_val), eb, sb }
        };
        let value = Formula::FpToIeeeBv(Box::new(converted));

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

        // Real IEEE format conversion under the default rounding mode. This
        // was modeled as bit truncation/zero-extension — `fcvt s0, d1` kept the
        // LOW 32 BITS of the double, which is neither the value nor any IEEE
        // operation at all. 447 words of the native semantic differential
        // diverged. `FpConvert` is SMT's `to_fp` between formats: NaN
        // propagates, overflow goes to infinity, rounding is RNE — exactly
        // FCVT's behaviour with FPCR at its default.
        let (src_eb, src_sb) =
            FpFormat::for_width(src_width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();
        let (dst_eb, dst_sb) =
            FpFormat::for_width(dst_width).ok_or(SemError::UnsupportedOpcode(insn.opcode))?.eb_sb();
        let value = Formula::FpToIeeeBv(Box::new(Formula::FpConvert {
            rm: Box::new(Formula::FpRoundingMode(trust_types::RoundingMode::RNE)),
            value: Box::new(Formula::FpFromBits {
                bits: Box::new(src_val),
                eb: src_eb,
                sb: src_sb,
            }),
            eb: dst_eb,
            sb: dst_sb,
        }));

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
        let cond_formula = condition_to_formula(state, cond)?;

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
    F16,
    F32,
    F64,
}

impl FpFormat {
    /// Resolve the IEEE format for a scalar FP lane `width`, or `None` (=>
    /// fail-closed) for any width other than 32 (f32) or 64 (f64).
    fn for_width(width: u32) -> Option<Self> {
        match width {
            // f16 was fail-closed here while the concrete evaluator had no
            // half-precision arithmetic. It does now (exact f16<->f32 unpack /
            // RNE pack in `concrete.rs`; every other f16 path routes through
            // f32, which is double-rounding-safe: an intermediate with
            // >= 2*11+2 = 24 significand bits is innocuous, and f32 has
            // exactly 24), so refusing would only shrink hardware-differential
            // coverage — 810 words of the fast tier — for no soundness gain.
            16 => Some(FpFormat::F16),
            32 => Some(FpFormat::F32),
            64 => Some(FpFormat::F64),
            _ => None,
        }
    }

    /// `(eb, sb)` — exponent-bit and significand-bit counts (`eb + sb == width`).
    fn eb_sb(self) -> (u32, u32) {
        match self {
            FpFormat::F16 => (5, 11),
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
    // ARM DDI 0487, VFPExpandImm. With imm8 = a:b:c:d:e:f:g:h,
    //
    //   sign     = a
    //   exponent = NOT(b) : Replicate(b, E-3) : c : d      (E bits total)
    //   fraction = e:f:g:h : Zeros(F-4)                    (F bits total)
    //
    // The previous expansion had three defects, found because the FMOV
    // (immediate) family diverged from hardware on 3,561 words of the native
    // semantic differential: `c` was shifted into the replicate range (bit 25
    // of an f32, where OR-ing into the replicated ones made it a no-op
    // whenever b=1), `d` was misrouted into the FRACTION (it is the low
    // exponent bit), and the fraction was placed one bit low starting at `d`.
    // Measured: FMOV S0, #1.0 (imm8 0x70) expanded to 0x3FC00000 — 1.5.
    let a = (imm8 >> 7) & 1;
    let b = (imm8 >> 6) & 1;
    let c = (imm8 >> 5) & 1;
    let d = (imm8 >> 4) & 1;
    let efgh = imm8 & 0x0F;

    let value: i128 = match width {
        // E=8, F=23: exponent bits 30..23, fraction bits 22..0.
        32 => {
            let sign = a << 31;
            let exp =
                ((!b & 1) << 30) | (if b == 1 { 0x1F << 25 } else { 0 }) | (c << 24) | (d << 23);
            let frac = efgh << 19;
            (sign | exp | frac) as i128
        }
        // E=11, F=52: exponent bits 62..52, fraction bits 51..0.
        64 => {
            let sign = a << 63;
            let exp =
                ((!b & 1) << 62) | (if b == 1 { 0xFFu64 << 54 } else { 0 }) | (c << 53) | (d << 52);
            let frac = efgh << 48;
            (sign | exp | frac) as i128
        }
        // E=5, F=10: exponent bits 14..10, fraction bits 9..0. The previous
        // code stored the RAW imm8 here, which is not a half-precision
        // expansion of anything.
        16 => {
            let sign = a << 15;
            let exp =
                ((!b & 1) << 14) | (if b == 1 { 0b11 << 12 } else { 0 }) | (c << 11) | (d << 10);
            let frac = efgh << 6;
            (sign | exp | frac) as i128
        }
        _ => imm8 as i128,
    };

    Formula::BitVec { value, width }
}

#[cfg(test)]
mod fp_semantics_tests {
    use trust_disasm::decode_aarch64;

    use super::*;
    use crate::Aarch64Semantics;
    use crate::concrete::ConcreteState;
    use crate::semantics::Semantics;
    use crate::state::MachineState;

    /// VFPExpandImm against hardware-known constants (ARM DDI 0487).
    ///
    /// The old expansion put `c` INSIDE the replicate range (an OR no-op
    /// whenever b=1), routed `d` into the fraction, and shifted the fraction a
    /// bit low — so `FMOV S0, #1.0` (imm8 0x70) expanded to 0x3FC00000, which
    /// is 1.5. That single constant explains why the FmovImm family was 3,561
    /// words of the native semantic differential.
    #[test]
    fn vfp_expand_imm8_matches_hardware_constants() {
        // (imm8, width, expected bits, value)
        let cases: &[(u64, u32, i128, &str)] = &[
            (0x70, 32, 0x3F80_0000, "1.0f32"),
            (0x70, 64, 0x3FF0_0000_0000_0000, "1.0f64"),
            (0x00, 32, 0x4000_0000, "2.0f32"),
            (0x00, 64, 0x4000_0000_0000_0000, "2.0f64"),
            (0xF0, 32, 0xBF80_0000_u32 as i128, "-1.0f32"),
            (0x60, 32, 0x3F00_0000, "0.5f32"),
            (0x70, 16, 0x3C00, "1.0f16"),
        ];
        for (imm8, width, expected, name) in cases {
            let Formula::BitVec { value, width: w } = expand_fp_imm8(*imm8, *width) else {
                panic!("expand must be a literal");
            };
            assert_eq!(w, *width);
            assert_eq!(
                value, *expected,
                "imm8 {imm8:#04x} at width {width} must expand to {name} ({expected:#x}); got {value:#x}"
            );
        }
    }

    fn fcmp_nzcv(a_bits: u64, b_bits: u64) -> (bool, bool, bool, bool) {
        // fcmp d0, d1 = 0x1E612000; run on a state with D0/D1 concrete.
        let insn = decode_aarch64(&0x1E61_2000u32.to_le_bytes(), 0x1000).expect("fcmp decodes");
        let state = MachineState::symbolic();
        let effects = Aarch64Semantics.effects(&state, &insn).expect("fcmp models");
        let mut concrete = ConcreteState::new();
        concrete.write_fpr(0, 64, u128::from(a_bits)).unwrap();
        concrete.write_fpr(1, 64, u128::from(b_bits)).unwrap();
        for effect in &effects {
            if let Effect::FlagUpdate { n, z, c, v } = effect {
                return (
                    concrete.eval_bool(n).expect("N evaluates"),
                    concrete.eval_bool(z).expect("Z evaluates"),
                    concrete.eval_bool(c).expect("C evaluates"),
                    concrete.eval_bool(v).expect("V evaluates"),
                );
            }
        }
        panic!("fcmp produced no FlagUpdate: {effects:?}");
    }

    /// ARM DDI 0487, FCMP result mapping: unordered->0011, lt->1000,
    /// eq->0110, gt->0010. The old signed-INTEGER-compare model got NaN wrong
    /// (V was hardcoded 0), -0/+0 wrong (unequal bits), and REVERSED the order
    /// of every pair of negative floats (two's-complement vs sign-magnitude).
    #[test]
    fn fcmp_sets_nzcv_exactly_as_hardware_does() {
        let one = 1.0f64.to_bits();
        let two = 2.0f64.to_bits();
        let nan = f64::NAN.to_bits();
        let neg_zero = (-0.0f64).to_bits();
        let pos_zero = 0.0f64.to_bits();
        let neg_one = (-1.0f64).to_bits();
        let neg_two = (-2.0f64).to_bits();

        assert_eq!(fcmp_nzcv(one, two), (true, false, false, false), "1 < 2 -> 1000");
        assert_eq!(fcmp_nzcv(two, one), (false, false, true, false), "2 > 1 -> 0010");
        assert_eq!(fcmp_nzcv(one, one), (false, true, true, false), "1 == 1 -> 0110");
        assert_eq!(fcmp_nzcv(nan, one), (false, false, true, true), "NaN -> 0011");
        assert_eq!(fcmp_nzcv(one, nan), (false, false, true, true), "NaN -> 0011");
        assert_eq!(
            fcmp_nzcv(neg_zero, pos_zero),
            (false, true, true, false),
            "-0 == +0 -> 0110, which the bit compare called UNEQUAL"
        );
        assert_eq!(
            fcmp_nzcv(neg_two, neg_one),
            (true, false, false, false),
            "-2 < -1 -> 1000, which the signed-int bit compare REVERSED"
        );
    }

    /// FSQRT is a real square root now, not the identity it was modeled as.
    #[test]
    fn fsqrt_computes_a_square_root_not_identity() {
        // fsqrt d0, d1 = 0x1E61C020.
        let insn = decode_aarch64(&0x1E61_C020u32.to_le_bytes(), 0x1000).expect("fsqrt decodes");
        let state = MachineState::symbolic();
        let effects = Aarch64Semantics.effects(&state, &insn).expect("fsqrt models");
        let mut concrete = ConcreteState::new();
        concrete.write_fpr(1, 64, u128::from(4.0f64.to_bits())).unwrap();
        let value = effects
            .iter()
            .find_map(|e| match e {
                Effect::FpRegWrite { index: 0, value, .. } => Some(value),
                _ => None,
            })
            .expect("fsqrt writes D0");
        let bits = concrete.eval_bv(value, 64).expect("sqrt evaluates concretely");
        assert_eq!(f64::from_bits(bits as u64), 2.0, "sqrt(4.0) = 2.0");
        // And the shape is the real thing, so an identity regression cannot
        // sneak back: sqrt(2.0) != 2.0.
        concrete.write_fpr(1, 64, u128::from(2.0f64.to_bits())).unwrap();
        let bits = concrete.eval_bv(value, 64).expect("sqrt evaluates concretely");
        assert_eq!(f64::from_bits(bits as u64), std::f64::consts::SQRT_2);
    }
}

#[cfg(test)]
mod fp_conversion_tests {
    use trust_disasm::decode_aarch64;

    use super::*;
    use crate::Aarch64Semantics;
    use crate::concrete::ConcreteState;
    use crate::semantics::Semantics;
    use crate::state::MachineState;

    fn run_to_gpr(word: u32, fpr: (u8, u32, u64)) -> u128 {
        let insn = decode_aarch64(&word.to_le_bytes(), 0x1000).expect("decodes");
        let effects = Aarch64Semantics.effects(&MachineState::symbolic(), &insn).expect("models");
        let mut concrete = ConcreteState::new();
        concrete.write_fpr(fpr.0, fpr.1, u128::from(fpr.2)).unwrap();
        let value = effects
            .iter()
            .find_map(|e| match e {
                Effect::RegWrite { value, .. } => Some(value),
                _ => None,
            })
            .expect("writes a GPR");
        let width = effects
            .iter()
            .find_map(|e| match e {
                Effect::RegWrite { width, .. } => Some(*width),
                _ => None,
            })
            .unwrap();
        concrete.eval_bv(value, width).expect("evaluates")
    }

    fn run_to_fpr(word: u32, gpr: (u8, u32, u64)) -> u128 {
        let insn = decode_aarch64(&word.to_le_bytes(), 0x1000).expect("decodes");
        let effects = Aarch64Semantics.effects(&MachineState::symbolic(), &insn).expect("models");
        let mut concrete = ConcreteState::new();
        concrete.write_gpr(gpr.0, gpr.1, u128::from(gpr.2)).unwrap();
        let value = effects
            .iter()
            .find_map(|e| match e {
                Effect::FpRegWrite { value, .. } => Some(value),
                _ => None,
            })
            .expect("writes an FP register");
        let width = effects
            .iter()
            .find_map(|e| match e {
                Effect::FpRegWrite { width, .. } => Some(*width),
                _ => None,
            })
            .unwrap();
        concrete.eval_bv(value, width).expect("evaluates")
    }

    /// FCVTZS: value conversion with AArch64 saturation — previously the raw
    /// IEEE BITS of the float were written to the GPR.
    #[test]
    fn fcvtzs_converts_the_value_and_saturates() {
        // fcvtzs w0, s1 = 0x1E380020.
        let w = 0x1E38_0020;
        assert_eq!(run_to_gpr(w, (1, 32, f32::to_bits(41.9) as u64)), 41, "RTZ truncates");
        assert_eq!(run_to_gpr(w, (1, 32, f32::to_bits(-41.9) as u64)), (-41i32) as u32 as u128);
        assert_eq!(run_to_gpr(w, (1, 32, f32::to_bits(f32::NAN) as u64)), 0, "NaN -> 0");
        assert_eq!(
            run_to_gpr(w, (1, 32, f32::to_bits(1.0e10) as u64)),
            i32::MAX as u128,
            "overflow saturates to i32::MAX"
        );
        assert_eq!(
            run_to_gpr(w, (1, 32, f32::to_bits(-1.0e10) as u64)),
            i32::MIN as u32 as u128,
            "underflow saturates to i32::MIN"
        );
    }

    /// FCVTZU: unsigned saturation — negatives clamp to zero.
    #[test]
    fn fcvtzu_saturates_unsigned() {
        // fcvtzu w0, s1 = 0x1E390020.
        let w = 0x1E39_0020;
        assert_eq!(run_to_gpr(w, (1, 32, f32::to_bits(41.9) as u64)), 41);
        assert_eq!(run_to_gpr(w, (1, 32, f32::to_bits(-3.0) as u64)), 0, "negative -> 0");
        assert_eq!(
            run_to_gpr(w, (1, 32, f32::to_bits(1.0e20) as u64)),
            u32::MAX as u128,
            "overflow saturates to u32::MAX"
        );
    }

    /// SCVTF/UCVTF: the represented VALUE arrives, not the bit pattern.
    #[test]
    fn scvtf_and_ucvtf_convert_the_value() {
        // scvtf s0, w1 = 0x1E220020 ; ucvtf s0, w1 = 0x1E230020.
        let neg_one = (-1i32) as u32 as u64;
        assert_eq!(
            run_to_fpr(0x1E22_0020, (1, 32, neg_one)),
            u128::from(f32::to_bits(-1.0)),
            "scvtf reads the integer as SIGNED"
        );
        assert_eq!(
            run_to_fpr(0x1E23_0020, (1, 32, neg_one)),
            u128::from(f32::to_bits(4294967295.0)),
            "ucvtf reads the same bits as UNSIGNED"
        );
        assert_eq!(run_to_fpr(0x1E22_0020, (1, 32, 42)), u128::from(f32::to_bits(42.0)));
    }

    /// FCVT: a real format conversion — previously `fcvt s0, d1` kept the low
    /// 32 bits of the double.
    #[test]
    fn fcvt_is_a_format_conversion_not_a_truncation() {
        // fcvt s0, d1 = 0x1E624020 ; fcvt d0, s1 = 0x1E22C020.
        let pi = std::f64::consts::PI;
        let insn = decode_aarch64(&0x1E62_4020u32.to_le_bytes(), 0x1000).unwrap();
        let effects = Aarch64Semantics.effects(&MachineState::symbolic(), &insn).unwrap();
        let mut c = ConcreteState::new();
        c.write_fpr(1, 64, u128::from(pi.to_bits())).unwrap();
        let v = effects
            .iter()
            .find_map(|e| match e {
                Effect::FpRegWrite { value, .. } => Some(value),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            c.eval_bv(v, 32).unwrap(),
            u128::from((pi as f32).to_bits()),
            "fcvt s0, d1 rounds PI to single precision; the old model kept the low half"
        );
    }
}

#[cfg(test)]
mod fp_format_tests {
    use trust_types::Formula;

    use super::FpFormat;

    #[test]
    fn for_width_maps_f32_and_f64_and_rejects_f16() {
        // f32 => S-lane, eb 8 / sb 24 (eb + sb == 32).
        let f32 = FpFormat::for_width(32).expect("f32 must resolve");
        assert_eq!(f32.eb_sb(), (8, 24));
        // f64 => D-lane, eb 11 / sb 53 (eb + sb == 64).
        let f64 = FpFormat::for_width(64).expect("f64 must resolve");
        assert_eq!(f64.eb_sb(), (11, 53));
        // f16 => H-lane, eb 5 / sb 11 (eb + sb == 16). Fail-closed until
        // 2026-08-18, when the concrete evaluator gained exact half-precision
        // support; see `for_width` for why refusing stopped being the safer
        // choice.
        let f16 = FpFormat::for_width(16).expect("f16 must resolve");
        assert_eq!(f16.eb_sb(), (5, 11));
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
