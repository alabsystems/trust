// trust-machine-sem: bounded concrete replay
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_disasm::operand::Condition;
use trust_types::{Formula, RoundingMode};

use crate::effect::Effect;

/// Concrete replay errors.
#[derive(Debug, thiserror::Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ConcreteError {
    /// The effect is outside the first bounded replay subset.
    #[error("unsupported effect: {0}")]
    UnsupportedEffect(&'static str),

    /// The formula is outside the first bounded replay subset.
    #[error("unsupported formula: {0}")]
    UnsupportedFormula(&'static str),

    /// A formula variable was not bound by the concrete state.
    #[error("unknown formula variable: {0}")]
    UnknownVariable(String),

    /// A concrete memory read touched an address that has not been initialized.
    #[error("uninitialized memory byte at 0x{address:x}")]
    UninitializedMemory { address: u64 },

    /// A memory effect used a width outside the bounded concrete replay subset.
    #[error("unsupported memory width in bytes: {0}")]
    UnsupportedMemoryWidth(u32),

    /// A memory effect range overflowed the 64-bit address space.
    #[error("memory access at 0x{address:x} with width {width_bytes} overflows address space")]
    MemoryAddressOverflow { address: u64, width_bytes: u32 },

    /// A bit-vector operation used an invalid width.
    #[error("invalid bit-vector width: {0}")]
    InvalidWidth(u32),

    /// A division or remainder formula evaluated with a zero divisor.
    #[error("division by zero")]
    DivisionByZero,

    /// A boolean formula was used where a bit-vector was required, or vice versa.
    #[error("formula sort mismatch: {0}")]
    SortMismatch(&'static str),
}

/// Concrete NZCV flags.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConcreteFlags {
    /// Negative flag.
    pub n: bool,
    /// Zero flag.
    pub z: bool,
    /// Carry flag.
    pub c: bool,
    /// Overflow flag.
    pub v: bool,
}

/// Concrete machine state for bounded straight-line replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteState {
    /// General-purpose registers X0-X30 / architecture register slots.
    pub gpr: [u64; 31],
    /// Stack pointer.
    pub sp: u64,
    /// Program counter.
    pub pc: u64,
    /// NZCV flags.
    pub flags: ConcreteFlags,
    /// SIMD/FP registers V0-V31, each a full 128-bit Q register.
    ///
    /// This file used to be ABSENT, and its absence was not neutral. With no
    /// V registers to read, `Effect::FpRegWrite` had to be refused and a
    /// `Formula::Var("V13")` had nowhere to resolve — so every SIMD-operand
    /// word was excluded from concrete replay, and the native semantic
    /// differential could not see that `str d13,[x28,#0xa0]` was modeled as
    /// storing the GPR X13. An oracle that cannot look at a register file
    /// cannot report a bug in it.
    pub fpr: [u128; 32],
    /// Initialized byte-addressed memory.
    pub memory: BTreeMap<u64, u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteValue {
    Bool(bool),
    Bv { value: u128, width: u32 },
}

/// Exact widening of an IEEE-754 binary16 bit pattern to `f32`.
///
/// Every f16 value is exactly representable in f32, so this is a bijection
/// onto its range; NaN payloads ride in the top fraction bits and are QUIETED,
/// which is what AArch64 does on every conversion and arithmetic use (FPCR.DN
/// at its default of 0 propagates the payload; the quiet bit is forced).
fn f16_bits_to_f32(h: u16) -> f32 {
    let sign = (u32::from(h) & 0x8000) << 16;
    let exp = (h >> 10) & 0x1F;
    let frac = u32::from(h & 0x3FF);
    let bits = match exp {
        0 => {
            if frac == 0 {
                sign
            } else {
                // Subnormal: value = frac * 2^-24. Normalise.
                // value = frac * 2^-24. After k normalising shifts the
                // significand is 1.xxx * 2^(-14-k), so the biased f32 exponent
                // is 113 - k — which the loop computes directly. (A first cut
                // subtracted one more here; the exhaustive round-trip test
                // caught 2^-24 widening to 2^-25 on its first run.)
                let mut e: u32 = 113; // biased f32 exponent of 2^-14
                let mut f = frac;
                while f & 0x400 == 0 {
                    f <<= 1;
                    e -= 1;
                }
                sign | (e << 23) | ((f & 0x3FF) << 13)
            }
        }
        0x1F => {
            if frac == 0 {
                sign | 0x7F80_0000
            } else {
                // NaN: payload widened, quiet bit forced.
                sign | 0x7F80_0000 | 0x0040_0000 | (frac << 13)
            }
        }
        _ => sign | ((u32::from(exp) + 112) << 23) | (frac << 13),
    };
    f32::from_bits(bits)
}

/// Round an `f32` to an IEEE-754 binary16 bit pattern, ties-to-even.
///
/// Handles subnormals (with correct rounding of the shifted-out bits),
/// overflow to infinity, and NaN (quiet bit forced, top nine payload bits
/// kept — ARM's FPConvertNaN). Rounding carries propagate naturally: a
/// mantissa that rounds up past its width bumps the exponent, and the largest
/// finite value rounding up lands exactly on the infinity encoding.
fn f32_to_f16_bits(x: f32) -> u16 {
    let bits = x.to_bits();
    let sign = ((bits >> 16) & 0x8000) as u16;
    let exp = ((bits >> 23) & 0xFF) as i32;
    let frac = bits & 0x7F_FFFF;
    if exp == 0xFF {
        return if frac == 0 {
            sign | 0x7C00
        } else {
            sign | 0x7C00 | 0x0200 | ((frac >> 13) as u16 & 0x1FF)
        };
    }
    let e16 = exp - 112; // rebias 127 -> 15
    if e16 >= 0x1F {
        return sign | 0x7C00; // overflow -> infinity
    }
    if e16 <= 0 {
        // Result is subnormal (or underflows to zero). The significand with
        // its hidden bit is shifted right; everything shifted out rounds.
        if e16 < -10 {
            return sign; // magnitude below half the smallest subnormal
        }
        let m = frac | 0x80_0000;
        let shift = (14 - e16) as u32;
        let val = m >> shift;
        let rem = m & ((1 << shift) - 1);
        let half = 1u32 << (shift - 1);
        let rounded = val + u32::from(rem > half || (rem == half && (val & 1) == 1));
        return sign | rounded as u16;
    }
    let val = frac >> 13;
    let rem = frac & 0x1FFF;
    let mut out = ((e16 as u32) << 10) | val;
    if rem > 0x1000 || (rem == 0x1000 && (val & 1) == 1) {
        out += 1;
    }
    sign | out as u16
}

/// Sign-extend a `width`-bit value to i128.
fn sign_extend_i128(value: u128, width: u32) -> i128 {
    if width == 0 || width >= 128 {
        return value as i128;
    }
    let shift = 128 - width;
    ((value as i128) << shift) >> shift
}

/// A concretely evaluated scalar float, format carried by the variant.
#[derive(Clone, Copy)]
enum FpVal {
    F32(f32),
    F64(f64),
}

impl Default for ConcreteState {
    fn default() -> Self {
        Self::new()
    }
}

impl ConcreteState {
    /// Create a zero-initialized concrete state.
    #[must_use]
    pub fn new() -> Self {
        Self {
            gpr: [0; 31],
            sp: 0,
            pc: 0,
            flags: ConcreteFlags::default(),
            fpr: [0; 32],
            memory: BTreeMap::new(),
        }
    }

    /// Read a concrete SIMD/FP register's low `width` bits.
    #[must_use]
    pub fn read_fpr(&self, index: u8, width: u32) -> u128 {
        if index >= 32 {
            return 0;
        }
        truncate(self.fpr[index as usize], width)
    }

    /// Write a concrete SIMD/FP register.
    ///
    /// A write of fewer than 128 bits ZEROES the upper lanes, which is the
    /// architectural behaviour of every scalar FP write in AArch64 and is what
    /// [`Effect::FpRegWrite`] documents. Preserving them would be the quiet
    /// version of the same bug this file exists to catch.
    pub fn write_fpr(&mut self, index: u8, width: u32, value: u128) -> Result<(), ConcreteError> {
        check_width(width)?;
        if index >= 32 {
            return Err(ConcreteError::InvalidWidth(u32::from(index)));
        }
        self.fpr[index as usize] = truncate(value, width);
        Ok(())
    }

    /// Read a concrete general-purpose register. Index 31 is the zero register.
    #[must_use]
    pub fn read_gpr(&self, index: u8, width: u32) -> u128 {
        if index >= 31 {
            return 0;
        }
        truncate(u128::from(self.gpr[index as usize]), width)
    }

    /// Write a concrete general-purpose register. Index 31 is discarded.
    pub fn write_gpr(&mut self, index: u8, width: u32, value: u128) -> Result<(), ConcreteError> {
        check_width(width)?;
        if index >= 31 {
            return Ok(());
        }
        self.gpr[index as usize] = truncate(value, width) as u64;
        Ok(())
    }

    /// Apply a sequence of effects in order.
    pub fn apply_effects(&mut self, effects: &[Effect]) -> Result<(), ConcreteError> {
        for effect in effects {
            self.apply_effect(effect)?;
        }
        Ok(())
    }

    /// Apply one effect.
    pub fn apply_effect(&mut self, effect: &Effect) -> Result<(), ConcreteError> {
        match effect {
            Effect::RegWrite { index, width, value } => {
                let value = self.eval_bv(value, *width)?;
                self.write_gpr(*index, *width, value)
            }
            Effect::SpWrite { value } => {
                self.sp = self.eval_bv(value, 64)? as u64;
                Ok(())
            }
            Effect::FlagUpdate { n, z, c, v } => {
                self.flags = ConcreteFlags {
                    n: self.eval_bool(n)?,
                    z: self.eval_bool(z)?,
                    c: self.eval_bool(c)?,
                    v: self.eval_bool(v)?,
                };
                Ok(())
            }
            Effect::PcUpdate { value } => {
                self.pc = self.eval_bv(value, 64)? as u64;
                Ok(())
            }
            Effect::MemRead { address, width_bytes } => {
                let address = self.eval_bv(address, 64)? as u64;
                self.load_memory_le(address, *width_bytes).map(|_| ())
            }
            Effect::MemWrite { address, value, width_bytes } => {
                let address = self.eval_bv(address, 64)? as u64;
                memory_bit_width(*width_bytes)?;
                // A store of `width_bytes` keeps the low `width_bytes*8` bits of the
                // value regardless of the value formula's own width: AArch64 STR of a
                // 32-bit store often sources a full 64-bit register formula. Evaluate
                // width-agnostically; `store_memory_le` truncates to the store width.
                let (value, _) = self.eval_bv_any(value)?;
                self.store_memory_le(address, *width_bytes, value)
            }
            Effect::ConditionalBranch { condition, target, fallthrough } => {
                let next_pc =
                    if eval_condition(self.flags, *condition) { target } else { fallthrough };
                self.pc = self.eval_bv(next_pc, 64)? as u64;
                Ok(())
            }
            Effect::Branch { .. } | Effect::Call { .. } | Effect::Return { .. } => {
                Err(ConcreteError::UnsupportedEffect("control flow"))
            }
            // MODELED, not refused. The value is a bit-pattern move into a
            // 128-bit lane with the upper bits zeroed — the same arithmetic
            // `write_gpr` does, over a different file. Refusing it was what
            // made every SIMD-operand word invisible to the concrete oracle.
            // IEEE-754 ARITHMETIC IS STILL NOT MODELED HERE: this executes the
            // `Formula` the semantics produced, and where that formula is a
            // bitvector approximation of an FP operation (FADD and friends in
            // `aarch64/fp.rs`) the approximation is what runs. What is now
            // exact is the DATA MOVEMENT class — FMOV between files, and the
            // SIMD&FP load/store forms — which is where the register-file
            // confusion lived.
            Effect::FpRegWrite { index, width, value } => {
                let value = self.eval_bv(value, *width)?;
                self.write_fpr(*index, *width, value)
            }
            // A barrier has no architectural SCALAR state consequence, and this
            // oracle is a single-threaded, in-order, sequentially-consistent
            // interpreter over `gpr`/`sp`/`pc`/`flags`/`memory` — it has no
            // reordering to constrain and no second observer to become visible
            // to. So `Ok(())` here is the barrier's real concrete semantics, not
            // a gap: the ONLY producers of this effect are DMB/DSB/ISB/CLREX
            // (`Aarch64Semantics::sem_barrier`), all of which emit exactly
            // `[Aarch64SyncBoundary, pc_advance]` — there is no data plane to
            // drop. CLREX's `clears_exclusive_monitor: true` is likewise inert
            // here because this state has no exclusive monitor to clear, and it
            // cannot acquire one: every exclusive instruction is refused
            // upstream (see the atomic arm below).
            Effect::Aarch64SyncBoundary { .. } => Ok(()),
            // Per-access ordering metadata whose DATA plane is carried by the
            // adjacent MemRead/RegWrite or MemWrite effect, so ignoring the
            // metadata loses nothing a scalar oracle could observe.
            //
            // That reasoning holds ONLY for the non-exclusive forms. An
            // exclusive access additionally reserves/checks the monitor and
            // (for STXR) writes a STATUS register that no adjacent effect
            // carries, so treating it as a no-op would silently invent success.
            // Measured: unreachable today — `Aarch64AtomicAccess` is produced
            // only by `sem_ldar`/`sem_stlr`, both hard-coding `exclusive:
            // false`, while LDXR/STXR/LDAXR/STLXR are refused with
            // `SemError::UnsupportedAtomic` before any effect is built. This
            // arm keeps that a CHECKED precondition rather than an assumption
            // the oracle silently depends on.
            Effect::Aarch64AtomicAccess { exclusive: false, .. } => Ok(()),
            Effect::Aarch64AtomicAccess { .. } => {
                Err(ConcreteError::UnsupportedEffect("exclusive atomic access"))
            }
        }
    }

    /// Apply one effect while evaluating its formula operands against an
    /// instruction pre-state.
    pub fn apply_effect_with_eval_state(
        &mut self,
        eval_state: &ConcreteState,
        effect: &Effect,
    ) -> Result<(), ConcreteError> {
        match effect {
            Effect::RegWrite { index, width, value } => {
                let value = eval_state.eval_bv(value, *width)?;
                self.write_gpr(*index, *width, value)
            }
            Effect::SpWrite { value } => {
                self.sp = eval_state.eval_bv(value, 64)? as u64;
                Ok(())
            }
            Effect::FlagUpdate { n, z, c, v } => {
                self.flags = ConcreteFlags {
                    n: eval_state.eval_bool(n)?,
                    z: eval_state.eval_bool(z)?,
                    c: eval_state.eval_bool(c)?,
                    v: eval_state.eval_bool(v)?,
                };
                Ok(())
            }
            Effect::PcUpdate { value } => {
                self.pc = eval_state.eval_bv(value, 64)? as u64;
                Ok(())
            }
            Effect::MemRead { address, width_bytes } => {
                let address = eval_state.eval_bv(address, 64)? as u64;
                eval_state.load_memory_le(address, *width_bytes).map(|_| ())
            }
            Effect::MemWrite { address, value, width_bytes } => {
                let address = eval_state.eval_bv(address, 64)? as u64;
                memory_bit_width(*width_bytes)?;
                // See apply_effect: store keeps low width_bytes*8 bits regardless of
                // the value formula's natural width; store_memory_le truncates.
                let (value, _) = eval_state.eval_bv_any(value)?;
                self.store_memory_le(address, *width_bytes, value)
            }
            Effect::ConditionalBranch { condition, target, fallthrough } => {
                let next_pc =
                    if eval_condition(eval_state.flags, *condition) { target } else { fallthrough };
                self.pc = eval_state.eval_bv(next_pc, 64)? as u64;
                Ok(())
            }
            Effect::Branch { .. } | Effect::Call { .. } | Effect::Return { .. } => {
                Err(ConcreteError::UnsupportedEffect("control flow"))
            }
            // See `apply_effect`: modeled as a zero-extending lane write.
            Effect::FpRegWrite { index, width, value } => {
                let value = eval_state.eval_bv(value, *width)?;
                self.write_fpr(*index, *width, value)
            }
            // A barrier has no architectural SCALAR state consequence, and this
            // oracle is a single-threaded, in-order, sequentially-consistent
            // interpreter over `gpr`/`sp`/`pc`/`flags`/`memory` — it has no
            // reordering to constrain and no second observer to become visible
            // to. So `Ok(())` here is the barrier's real concrete semantics, not
            // a gap: the ONLY producers of this effect are DMB/DSB/ISB/CLREX
            // (`Aarch64Semantics::sem_barrier`), all of which emit exactly
            // `[Aarch64SyncBoundary, pc_advance]` — there is no data plane to
            // drop. CLREX's `clears_exclusive_monitor: true` is likewise inert
            // here because this state has no exclusive monitor to clear, and it
            // cannot acquire one: every exclusive instruction is refused
            // upstream (see the atomic arm below).
            Effect::Aarch64SyncBoundary { .. } => Ok(()),
            // Per-access ordering metadata whose DATA plane is carried by the
            // adjacent MemRead/RegWrite or MemWrite effect, so ignoring the
            // metadata loses nothing a scalar oracle could observe.
            //
            // That reasoning holds ONLY for the non-exclusive forms. An
            // exclusive access additionally reserves/checks the monitor and
            // (for STXR) writes a STATUS register that no adjacent effect
            // carries, so treating it as a no-op would silently invent success.
            // Measured: unreachable today — `Aarch64AtomicAccess` is produced
            // only by `sem_ldar`/`sem_stlr`, both hard-coding `exclusive:
            // false`, while LDXR/STXR/LDAXR/STLXR are refused with
            // `SemError::UnsupportedAtomic` before any effect is built. This
            // arm keeps that a CHECKED precondition rather than an assumption
            // the oracle silently depends on.
            Effect::Aarch64AtomicAccess { exclusive: false, .. } => Ok(()),
            Effect::Aarch64AtomicAccess { .. } => {
                Err(ConcreteError::UnsupportedEffect("exclusive atomic access"))
            }
        }
    }

    /// Evaluate a formula as a concrete bit-vector with the expected width.
    pub fn eval_bv(&self, formula: &Formula, expected_width: u32) -> Result<u128, ConcreteError> {
        // Existing machine-sem producers use both SMT-style extension amounts
        // and target widths. The expected width disambiguates without relaxing
        // unrelated bit-vector width checks.
        match formula {
            Formula::BvZeroExt(inner, amount_or_width) => {
                return self.eval_bv_extension(inner, *amount_or_width, expected_width, false);
            }
            Formula::BvSignExt(inner, amount_or_width) => {
                return self.eval_bv_extension(inner, *amount_or_width, expected_width, true);
            }
            _ => {}
        }
        match self.eval_formula(formula)? {
            ConcreteValue::Bv { value, width } if width == expected_width => Ok(value),
            ConcreteValue::Bv { .. } => Err(ConcreteError::SortMismatch("bit-vector width")),
            ConcreteValue::Bool(_) => Err(ConcreteError::SortMismatch("expected bit-vector")),
        }
    }

    /// Evaluate a formula as a concrete boolean.
    pub fn eval_bool(&self, formula: &Formula) -> Result<bool, ConcreteError> {
        match self.eval_formula(formula)? {
            ConcreteValue::Bool(value) => Ok(value),
            ConcreteValue::Bv { .. } => Err(ConcreteError::SortMismatch("expected bool")),
        }
    }

    /// Store a little-endian concrete value into initialized byte memory.
    pub fn store_memory_le(
        &mut self,
        address: u64,
        width_bytes: u32,
        value: u128,
    ) -> Result<(), ConcreteError> {
        let width = memory_bit_width(width_bytes)?;
        let value = truncate(value, width);
        for offset in 0..width_bytes {
            let byte_address = checked_byte_address(address, offset, width_bytes)?;
            let byte = ((value >> (offset * 8)) & 0xff) as u8;
            self.memory.insert(byte_address, byte);
        }
        Ok(())
    }

    /// Load a little-endian concrete value from initialized byte memory.
    pub fn load_memory_le(&self, address: u64, width_bytes: u32) -> Result<u128, ConcreteError> {
        memory_bit_width(width_bytes)?;
        let mut value = 0u128;
        for offset in 0..width_bytes {
            let byte_address = checked_byte_address(address, offset, width_bytes)?;
            let Some(byte) = self.memory.get(&byte_address) else {
                return Err(ConcreteError::UninitializedMemory { address: byte_address });
            };
            value |= u128::from(*byte) << (offset * 8);
        }
        Ok(value)
    }

    fn eval_formula(&self, formula: &Formula) -> Result<ConcreteValue, ConcreteError> {
        match formula {
            Formula::Bool(value) => Ok(ConcreteValue::Bool(*value)),
            Formula::BitVec { value, width } => {
                check_width(*width)?;
                Ok(ConcreteValue::Bv { value: truncate_i128(*value, *width), width: *width })
            }
            Formula::Var(name, _) => self.eval_var(name),
            Formula::SymVar(sym, _) => self.eval_var(sym.as_str()),
            Formula::Not(inner) => Ok(ConcreteValue::Bool(!self.eval_bool(inner)?)),
            Formula::And(terms) => {
                for term in terms {
                    if !self.eval_bool(term)? {
                        return Ok(ConcreteValue::Bool(false));
                    }
                }
                Ok(ConcreteValue::Bool(true))
            }
            Formula::Or(terms) => {
                for term in terms {
                    if self.eval_bool(term)? {
                        return Ok(ConcreteValue::Bool(true));
                    }
                }
                Ok(ConcreteValue::Bool(false))
            }
            Formula::Eq(lhs, rhs) => {
                Ok(ConcreteValue::Bool(self.eval_formula(lhs)? == self.eval_formula(rhs)?))
            }
            Formula::BvAdd(lhs, rhs, width) => {
                self.eval_bv_binop(lhs, rhs, *width, |a, b| a.wrapping_add(b))
            }
            Formula::BvSub(lhs, rhs, width) => {
                self.eval_bv_binop(lhs, rhs, *width, |a, b| a.wrapping_sub(b))
            }
            Formula::BvMul(lhs, rhs, width) => {
                self.eval_bv_binop(lhs, rhs, *width, |a, b| a.wrapping_mul(b))
            }
            Formula::BvAnd(lhs, rhs, width) => self.eval_bv_binop(lhs, rhs, *width, |a, b| a & b),
            Formula::BvOr(lhs, rhs, width) => self.eval_bv_binop(lhs, rhs, *width, |a, b| a | b),
            Formula::BvXor(lhs, rhs, width) => self.eval_bv_binop(lhs, rhs, *width, |a, b| a ^ b),
            Formula::BvNot(inner, width) => {
                check_width(*width)?;
                Ok(ConcreteValue::Bv {
                    value: truncate(!self.eval_bv(inner, *width)?, *width),
                    width: *width,
                })
            }
            Formula::BvShl(lhs, rhs, width) => {
                self.eval_bv_shift(lhs, rhs, *width, |a, shift| a.checked_shl(shift).unwrap_or(0))
            }
            Formula::BvLShr(lhs, rhs, width) => {
                self.eval_bv_shift(lhs, rhs, *width, |a, shift| a.checked_shr(shift).unwrap_or(0))
            }
            Formula::BvAShr(lhs, rhs, width) => {
                check_width(*width)?;
                let lhs = self.eval_bv(lhs, *width)?;
                let shift = self.eval_shift(rhs, *width)?;
                let value = if shift >= *width {
                    if sign_bit(lhs, *width) { mask(*width) } else { 0 }
                } else {
                    truncate(signed_to_i128(lhs, *width).wrapping_shr(shift) as u128, *width)
                };
                Ok(ConcreteValue::Bv { value, width: *width })
            }
            Formula::BvUDiv(lhs, rhs, width) => {
                self.eval_bv_div(lhs, rhs, *width, false, |a, b| a / b)
            }
            Formula::BvURem(lhs, rhs, width) => {
                self.eval_bv_div(lhs, rhs, *width, false, |a, b| a % b)
            }
            Formula::BvSDiv(lhs, rhs, width) => self.eval_bv_sdiv(lhs, rhs, *width, false),
            Formula::BvSRem(lhs, rhs, width) => self.eval_bv_sdiv(lhs, rhs, *width, true),
            Formula::BvULt(lhs, rhs, width) => {
                Ok(ConcreteValue::Bool(self.eval_bv(lhs, *width)? < self.eval_bv(rhs, *width)?))
            }
            Formula::BvULe(lhs, rhs, width) => {
                Ok(ConcreteValue::Bool(self.eval_bv(lhs, *width)? <= self.eval_bv(rhs, *width)?))
            }
            Formula::BvSLt(lhs, rhs, width) => Ok(ConcreteValue::Bool(
                signed_to_i128(self.eval_bv(lhs, *width)?, *width)
                    < signed_to_i128(self.eval_bv(rhs, *width)?, *width),
            )),
            Formula::BvSLe(lhs, rhs, width) => Ok(ConcreteValue::Bool(
                signed_to_i128(self.eval_bv(lhs, *width)?, *width)
                    <= signed_to_i128(self.eval_bv(rhs, *width)?, *width),
            )),
            Formula::BvExtract { inner, high, low } => {
                if low > high {
                    return Err(ConcreteError::InvalidWidth(0));
                }
                let width = high - low + 1;
                check_width(width)?;
                let (source, source_width) = self.eval_bv_any(inner)?;
                if *high >= source_width {
                    return Err(ConcreteError::InvalidWidth(width));
                }
                Ok(ConcreteValue::Bv { value: truncate(source >> low, width), width })
            }
            Formula::BvConcat(lhs, rhs) => {
                let (lhs_value, lhs_width) = self.eval_bv_any(lhs)?;
                let (rhs_value, rhs_width) = self.eval_bv_any(rhs)?;
                let width = lhs_width + rhs_width;
                check_width(width)?;
                Ok(ConcreteValue::Bv {
                    value: truncate((lhs_value << rhs_width) | rhs_value, width),
                    width,
                })
            }
            Formula::BvZeroExt(inner, width) => {
                let (value, inner_width) = self.eval_bv_any(inner)?;
                let target_width = extension_target_width(inner_width, *width)?;
                Ok(ConcreteValue::Bv { value: truncate(value, target_width), width: target_width })
            }
            Formula::BvSignExt(inner, width) => {
                let (value, inner_width) = self.eval_bv_any(inner)?;
                let target_width = extension_target_width(inner_width, *width)?;
                let extended = if sign_bit(value, inner_width) {
                    value | (mask(target_width) ^ mask(inner_width))
                } else {
                    value
                };
                Ok(ConcreteValue::Bv {
                    value: truncate(extended, target_width),
                    width: target_width,
                })
            }
            Formula::Ite(cond, then_value, else_value) => {
                if self.eval_bool(cond)? {
                    self.eval_formula(then_value)
                } else {
                    self.eval_formula(else_value)
                }
            }
            Formula::Select(array, index) if self.is_concrete_memory_array(array) => {
                let address = self.eval_bv(index, 64)? as u64;
                Ok(ConcreteValue::Bv { value: self.load_memory_le(address, 1)?, width: 8 })
            }
            Formula::Select(..) | Formula::Store(..) => {
                Err(ConcreteError::UnsupportedFormula("memory array"))
            }
            // The ONE FP shape the AArch64 semantics emit. See
            // `eval_fp_binop_round_trip` for what this does and does not settle.
            Formula::FpToIeeeBv(inner) => self.eval_fp_binop_round_trip(inner),
            // FCMP's NZCV predicates. Rust's `<` / `==` on floats are IEEE
            // `fp.lt` / `fp.eq` exactly: false on any NaN operand, and
            // -0.0 == +0.0. Shape-restricted like everything FP here — the
            // operands must be `FpFromBits` of one matching format, or the node
            // is refused rather than approximated.
            Formula::FpLt(a, b) => {
                let (x, y) = self.eval_fp_pair(a, b)?;
                Ok(ConcreteValue::Bool(match (x, y) {
                    (FpVal::F32(x), FpVal::F32(y)) => x < y,
                    (FpVal::F64(x), FpVal::F64(y)) => x < y,
                    _ => unreachable!("eval_fp_pair enforces matching formats"),
                }))
            }
            Formula::FpEq(a, b) => {
                let (x, y) = self.eval_fp_pair(a, b)?;
                Ok(ConcreteValue::Bool(match (x, y) {
                    (FpVal::F32(x), FpVal::F32(y)) => x == y,
                    (FpVal::F64(x), FpVal::F64(y)) => x == y,
                    _ => unreachable!("eval_fp_pair enforces matching formats"),
                }))
            }
            // The five conversion nodes. Rust's casts are EXACTLY the
            // semantics being modeled: float -> int `as` saturates with
            // NaN -> 0 (the AArch64 FCVTZ* behaviour the nodes are DEFINED to
            // have — they are total, unlike SMT's fp.to_sbv), int -> float
            // rounds RNE, and f64 -> f32 `as` rounds RNE with overflow to
            // infinity. Same is-the-operation-itself caveat as the arithmetic.
            Formula::FpToSbv { rm, value, width, .. } => {
                if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RTZ)) {
                    return Err(ConcreteError::UnsupportedFormula(
                        "FP-to-int rounding mode other than RTZ",
                    ));
                }
                let (bits, fmt) = self.eval_fp_from_bits(value)?;
                let wide: i128 = match fmt {
                    (5, 11) => f16_bits_to_f32(bits as u16) as i128,
                    (8, 24) => f32::from_bits(bits as u32) as i128,
                    (11, 53) => f64::from_bits(bits as u64) as i128,
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64"));
                    }
                };
                let (min, max) = match width {
                    32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
                    64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula(
                            "FCVTZS width outside 32/64",
                        ));
                    }
                };
                let clamped = wide.clamp(min, max);
                let mask = if *width == 128 { u128::MAX } else { (1u128 << width) - 1 };
                Ok(ConcreteValue::Bv { value: (clamped as u128) & mask, width: *width })
            }
            Formula::FpToUbv { rm, value, width, .. } => {
                if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RTZ)) {
                    return Err(ConcreteError::UnsupportedFormula(
                        "FP-to-int rounding mode other than RTZ",
                    ));
                }
                let (bits, fmt) = self.eval_fp_from_bits(value)?;
                let wide: u128 = match fmt {
                    (5, 11) => f16_bits_to_f32(bits as u16) as u128,
                    (8, 24) => f32::from_bits(bits as u32) as u128,
                    (11, 53) => f64::from_bits(bits as u64) as u128,
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64"));
                    }
                };
                let max = match width {
                    32 => u128::from(u32::MAX),
                    64 => u128::from(u64::MAX),
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula(
                            "FCVTZU width outside 32/64",
                        ));
                    }
                };
                Ok(ConcreteValue::Bv { value: wide.min(max), width: *width })
            }
            Formula::FpFromSbv { rm, value, eb, sb } | Formula::FpFromUbv { rm, value, eb, sb } => {
                if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RNE)) {
                    return Err(ConcreteError::UnsupportedFormula(
                        "int-to-FP rounding mode other than RNE",
                    ));
                }
                let signed = matches!(formula, Formula::FpFromSbv { .. });
                let (int_bits, int_width) = self.eval_bv_any(value)?;
                let result_bits: u128 = match (eb, sb) {
                    (5, 11) => {
                        // Via f32: the intermediate's 24 significand bits meet
                        // Figueroa's 2p+2 bound for p = 11, so the double
                        // rounding is exact.
                        let x: f32 = if signed {
                            (sign_extend_i128(int_bits, int_width)) as f32
                        } else {
                            int_bits as f32
                        };
                        u128::from(f32_to_f16_bits(x))
                    }
                    (8, 24) => {
                        let x: f32 = if signed {
                            (sign_extend_i128(int_bits, int_width)) as f32
                        } else {
                            int_bits as f32
                        };
                        u128::from(x.to_bits())
                    }
                    (11, 53) => {
                        let x: f64 = if signed {
                            (sign_extend_i128(int_bits, int_width)) as f64
                        } else {
                            int_bits as f64
                        };
                        u128::from(x.to_bits())
                    }
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64"));
                    }
                };
                // The node's sort is Float; wrap back to bits only via
                // FpToIeeeBv, which arrives here as the parent. Represent the
                // float VALUE by its bit pattern at the format's width.
                Ok(ConcreteValue::Bv { value: result_bits, width: eb + sb })
            }
            Formula::FpConvert { rm, value, eb, sb } => {
                if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RNE)) {
                    return Err(ConcreteError::UnsupportedFormula(
                        "FP format conversion rounding mode other than RNE",
                    ));
                }
                let (bits, fmt) = self.eval_fp_from_bits(value)?;
                let result_bits: u128 = match (fmt, (*eb, *sb)) {
                    ((8, 24), (11, 53)) => {
                        u128::from((f64::from(f32::from_bits(bits as u32))).to_bits())
                    }
                    ((11, 53), (8, 24)) => {
                        u128::from((f64::from_bits(bits as u64) as f32).to_bits())
                    }
                    // f16 widenings are exact; narrowings go via f32, which is
                    // Figueroa-safe for p = 11 (see the binop lane).
                    ((5, 11), (8, 24)) => u128::from(f16_bits_to_f32(bits as u16).to_bits()),
                    ((5, 11), (11, 53)) => {
                        u128::from(f64::from(f16_bits_to_f32(bits as u16)).to_bits())
                    }
                    ((8, 24), (5, 11)) => u128::from(f32_to_f16_bits(f32::from_bits(bits as u32))),
                    ((11, 53), (5, 11)) => {
                        u128::from(f32_to_f16_bits(f64::from_bits(bits as u64) as f32))
                    }
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula(
                            "FP conversion outside f32<->f64",
                        ));
                    }
                };
                Ok(ConcreteValue::Bv { value: result_bits, width: eb + sb })
            }
            Formula::FpIsNaN(a) => {
                let (bits, fmt) = self.eval_fp_from_bits(a)?;
                Ok(ConcreteValue::Bool(match fmt {
                    (5, 11) => f16_bits_to_f32(bits as u16).is_nan(),
                    (8, 24) => f32::from_bits(bits as u32).is_nan(),
                    (11, 53) => f64::from_bits(bits as u64).is_nan(),
                    _ => {
                        return Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64"));
                    }
                }))
            }
            Formula::Int(_)
            | Formula::UInt(_)
            | Formula::Implies(..)
            | Formula::Lt(..)
            | Formula::Le(..)
            | Formula::Gt(..)
            | Formula::Ge(..)
            | Formula::Add(..)
            | Formula::Sub(..)
            | Formula::Mul(..)
            | Formula::Div(..)
            | Formula::Rem(..)
            | Formula::Neg(..)
            | Formula::BvToInt(..)
            | Formula::IntToBv(..)
            | Formula::Forall(..)
            | Formula::Exists(..) => Err(ConcreteError::UnsupportedFormula("formula kind")),
            _ => Err(ConcreteError::UnsupportedFormula("formula kind")),
        }
    }

    fn eval_var(&self, name: &str) -> Result<ConcreteValue, ConcreteError> {
        if let Some(index) = name.strip_prefix('X').and_then(|suffix| suffix.parse::<usize>().ok())
            && index < self.gpr.len()
        {
            return Ok(ConcreteValue::Bv { value: u128::from(self.gpr[index]), width: 64 });
        }

        // THE FLAG NAMES ARE MATCHED FIRST, DELIBERATELY. `V` is the overflow
        // flag AND the prefix of every SIMD register name, so the order here is
        // load-bearing: a `Vn` arm placed above this match would still not
        // capture bare `V` (the empty suffix does not parse as a number), but
        // relying on that is relying on an accident of `str::parse`. Matching
        // the four flag names exactly, first, makes the split explicit.
        match name {
            "SP" => return Ok(ConcreteValue::Bv { value: u128::from(self.sp), width: 64 }),
            "PC" => return Ok(ConcreteValue::Bv { value: u128::from(self.pc), width: 64 }),
            "N" | "_N" => return Ok(ConcreteValue::Bool(self.flags.n)),
            "Z" | "_Z" => return Ok(ConcreteValue::Bool(self.flags.z)),
            "C" | "_C" => return Ok(ConcreteValue::Bool(self.flags.c)),
            "V" | "_V" => return Ok(ConcreteValue::Bool(self.flags.v)),
            _ => {}
        }

        // `MachineState::symbolic` names the SIMD/FP file `V0`..`V31` at 128
        // bits; `read_fpr` narrows with a `BvExtract`, so the variable itself is
        // always the full Q register.
        if let Some(index) = name.strip_prefix('V').and_then(|suffix| suffix.parse::<usize>().ok())
            && index < self.fpr.len()
        {
            return Ok(ConcreteValue::Bv { value: self.fpr[index], width: 128 });
        }

        Err(ConcreteError::UnknownVariable(name.to_owned()))
    }

    /// Evaluate the ONE FP formula shape `aarch64/fp.rs` emits:
    ///
    /// ```text
    /// FpToIeeeBv( Fp{Add,Sub,Mul,Div}( FpRoundingMode(RNE),
    ///                                  FpFromBits{a, eb, sb},
    ///                                  FpFromBits{b, eb, sb} ) )
    /// ```
    ///
    /// WHY THIS EXISTS. Before it, every FP `Formula` node fell through to
    /// `UnsupportedFormula`, so `FADD`/`FSUB`/`FMUL`/`FDIV` could not be
    /// replayed — and the native semantic differential reported them as
    /// `unchecked`, not as agreeing. They are not a small class: the
    /// stratified full-tier population carries 3,000 words of EACH, all four
    /// accepted by `Aarch64Semantics` and therefore all four reachable by the
    /// output gate, with nothing anywhere having compared one against a CPU.
    /// The crate header calls them "BIT-EXACT IEEE-754"; that claim had never
    /// been measured.
    ///
    /// WHAT IT SETTLES, AND WHAT IT DOES NOT. Rust's `f32`/`f64` `+ - * /`
    /// compile to the host's `fadd`/`fsub`/`fmul`/`fdiv` under the default
    /// rounding mode, which is exactly the operation being modeled — so this
    /// evaluator does NOT independently verify IEEE arithmetic, and a
    /// differential built on it cannot. What it DOES check is everything
    /// around the arithmetic, which is where every bug in this program has
    /// actually lived: which register file each operand comes from, which lane
    /// and how wide, whether the upper lanes of the destination are zeroed,
    /// whether the destination is the register the instruction names, and
    /// whether any flag or memory effect was invented or lost. That is the
    /// `str d13` class, and it was reachable.
    ///
    /// SHAPE-RESTRICTED ON PURPOSE. Anything that is not this exact tree — a
    /// non-RNE rounding mode, mismatched formats, an `FpSqrt`, an `FpFma`, a
    /// bare `FpFromBits` — is REFUSED and reported unchecked, rather than
    /// approximated onto the nearest thing this function can compute. A widened
    /// evaluator that quietly answered for a shape the semantics do not emit
    /// would make the differential agree with itself.
    fn eval_fp_binop_round_trip(&self, inner: &Formula) -> Result<ConcreteValue, ConcreteError> {
        #[derive(Clone, Copy)]
        enum Op {
            Add,
            Sub,
            Mul,
            Div,
        }
        // The int->FP and format conversions produce a FLOAT value that this
        // evaluator represents by its bit pattern, which is exactly what
        // `FpToIeeeBv` asks for — so they route straight through.
        if matches!(
            inner,
            Formula::FpFromSbv { .. } | Formula::FpFromUbv { .. } | Formula::FpConvert { .. }
        ) {
            return self.eval_formula(inner);
        }
        // FSQRT: unary, same round-trip discipline. Rust's `sqrt` lowers to
        // the host's `fsqrt`, which IEEE-754 requires to be correctly rounded —
        // the same is-the-operation-itself caveat as the binops below.
        if let Formula::FpSqrt(rm, a) = inner {
            if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RNE)) {
                return Err(ConcreteError::UnsupportedFormula("FP rounding mode other than RNE"));
            }
            let (a_bits, a_fmt) = self.eval_fp_from_bits(a)?;
            return match a_fmt {
                (5, 11) => Ok(ConcreteValue::Bv {
                    value: u128::from(f32_to_f16_bits(f16_bits_to_f32(a_bits as u16).sqrt())),
                    width: 16,
                }),
                (8, 24) => Ok(ConcreteValue::Bv {
                    value: u128::from(f32::from_bits(a_bits as u32).sqrt().to_bits()),
                    width: 32,
                }),
                (11, 53) => Ok(ConcreteValue::Bv {
                    value: u128::from(f64::from_bits(a_bits as u64).sqrt().to_bits()),
                    width: 64,
                }),
                _ => Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64")),
            };
        }
        let (op, rm, a, b) = match inner {
            Formula::FpAdd(rm, a, b) => (Op::Add, rm, a, b),
            Formula::FpSub(rm, a, b) => (Op::Sub, rm, a, b),
            Formula::FpMul(rm, a, b) => (Op::Mul, rm, a, b),
            Formula::FpDiv(rm, a, b) => (Op::Div, rm, a, b),
            _ => return Err(ConcreteError::UnsupportedFormula("FP op outside the modeled set")),
        };
        if !matches!(**rm, Formula::FpRoundingMode(RoundingMode::RNE)) {
            // Rust's float operators are RNE and nothing here can change the
            // host's FPCR, so any other mode would be evaluated WRONG rather
            // than not at all.
            return Err(ConcreteError::UnsupportedFormula("FP rounding mode other than RNE"));
        }
        let (a_bits, a_fmt) = self.eval_fp_from_bits(a)?;
        let (b_bits, b_fmt) = self.eval_fp_from_bits(b)?;
        if a_fmt != b_fmt {
            return Err(ConcreteError::UnsupportedFormula("mixed FP formats in one operation"));
        }
        let (value, width) = match a_fmt {
            // binary16, computed in f32 and narrowed. EXACT, not approximate:
            // performing a +,-,*,/ (or sqrt) in precision q and then rounding
            // to precision p is identical to rounding the true result directly
            // to p whenever q >= 2p+2 (Figueroa); f32's 24 significand bits
            // meet the bound for p = 11 exactly.
            (5, 11) => {
                let x = f16_bits_to_f32(a_bits as u16);
                let y = f16_bits_to_f32(b_bits as u16);
                let r = match op {
                    Op::Add => x + y,
                    Op::Sub => x - y,
                    Op::Mul => x * y,
                    Op::Div => x / y,
                };
                (u128::from(f32_to_f16_bits(r)), 16)
            }
            (8, 24) => {
                let x = f32::from_bits(a_bits as u32);
                let y = f32::from_bits(b_bits as u32);
                let r = match op {
                    Op::Add => x + y,
                    Op::Sub => x - y,
                    Op::Mul => x * y,
                    Op::Div => x / y,
                };
                (u128::from(r.to_bits()), 32)
            }
            (11, 53) => {
                let x = f64::from_bits(a_bits as u64);
                let y = f64::from_bits(b_bits as u64);
                let r = match op {
                    Op::Add => x + y,
                    Op::Sub => x - y,
                    Op::Mul => x * y,
                    Op::Div => x / y,
                };
                (u128::from(r.to_bits()), 64)
            }
            _ => return Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64")),
        };
        Ok(ConcreteValue::Bv { value, width })
    }

    /// Evaluate two `FpFromBits` operands of ONE matching scalar format.
    fn eval_fp_pair(&self, a: &Formula, b: &Formula) -> Result<(FpVal, FpVal), ConcreteError> {
        let (a_bits, a_fmt) = self.eval_fp_from_bits(a)?;
        let (b_bits, b_fmt) = self.eval_fp_from_bits(b)?;
        if a_fmt != b_fmt {
            return Err(ConcreteError::UnsupportedFormula("mixed FP formats in one comparison"));
        }
        match a_fmt {
            // Exact widening: comparison in f32 is the f16 comparison.
            (5, 11) => Ok((
                FpVal::F32(f16_bits_to_f32(a_bits as u16)),
                FpVal::F32(f16_bits_to_f32(b_bits as u16)),
            )),
            (8, 24) => Ok((
                FpVal::F32(f32::from_bits(a_bits as u32)),
                FpVal::F32(f32::from_bits(b_bits as u32)),
            )),
            (11, 53) => Ok((
                FpVal::F64(f64::from_bits(a_bits as u64)),
                FpVal::F64(f64::from_bits(b_bits as u64)),
            )),
            _ => Err(ConcreteError::UnsupportedFormula("FP format outside f32/f64")),
        }
    }

    /// Evaluate an `FpFromBits` operand, returning `(bits, (eb, sb))`.
    ///
    /// The bit pattern must be exactly `eb + sb` bits wide — the format's own
    /// width. A mismatch means the semantics built a lane of the wrong size,
    /// which is a finding, so it is REFUSED here rather than truncated into
    /// agreement.
    fn eval_fp_from_bits(&self, formula: &Formula) -> Result<(u128, (u32, u32)), ConcreteError> {
        let Formula::FpFromBits { bits, eb, sb } = formula else {
            return Err(ConcreteError::UnsupportedFormula("FP operand is not FpFromBits"));
        };
        let width = eb + sb;
        let (value, got) = self.eval_bv_any(bits)?;
        if got != width {
            return Err(ConcreteError::SortMismatch("FpFromBits operand width"));
        }
        Ok((value, (*eb, *sb)))
    }

    fn eval_bv_any(&self, formula: &Formula) -> Result<(u128, u32), ConcreteError> {
        match self.eval_formula(formula)? {
            ConcreteValue::Bv { value, width } => Ok((value, width)),
            ConcreteValue::Bool(_) => Err(ConcreteError::SortMismatch("expected bit-vector")),
        }
    }

    fn eval_bv_binop(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        op: impl FnOnce(u128, u128) -> u128,
    ) -> Result<ConcreteValue, ConcreteError> {
        check_width(width)?;
        let value = op(self.eval_bv(lhs, width)?, self.eval_bv(rhs, width)?);
        Ok(ConcreteValue::Bv { value: truncate(value, width), width })
    }

    fn eval_bv_shift(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        op: impl FnOnce(u128, u32) -> u128,
    ) -> Result<ConcreteValue, ConcreteError> {
        check_width(width)?;
        let value = op(self.eval_bv(lhs, width)?, self.eval_shift(rhs, width)?);
        Ok(ConcreteValue::Bv { value: truncate(value, width), width })
    }

    fn eval_shift(&self, formula: &Formula, width: u32) -> Result<u32, ConcreteError> {
        Ok(self.eval_bv(formula, width)?.min(u128::from(u32::MAX)) as u32)
    }

    fn eval_bv_div(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        _signed: bool,
        op: impl FnOnce(u128, u128) -> u128,
    ) -> Result<ConcreteValue, ConcreteError> {
        check_width(width)?;
        let rhs = self.eval_bv(rhs, width)?;
        if rhs == 0 {
            return Err(ConcreteError::DivisionByZero);
        }
        let value = op(self.eval_bv(lhs, width)?, rhs);
        Ok(ConcreteValue::Bv { value: truncate(value, width), width })
    }

    fn eval_bv_sdiv(
        &self,
        lhs: &Formula,
        rhs: &Formula,
        width: u32,
        rem: bool,
    ) -> Result<ConcreteValue, ConcreteError> {
        check_width(width)?;
        let rhs = self.eval_bv(rhs, width)?;
        if rhs == 0 {
            return Err(ConcreteError::DivisionByZero);
        }
        let lhs = signed_to_i128(self.eval_bv(lhs, width)?, width);
        let rhs = signed_to_i128(rhs, width);
        let value = if rem { lhs.wrapping_rem(rhs) } else { lhs.wrapping_div(rhs) };
        Ok(ConcreteValue::Bv { value: truncate_i128(value, width), width })
    }

    fn eval_bv_extension(
        &self,
        inner: &Formula,
        amount_or_width: u32,
        expected_width: u32,
        sign_extend: bool,
    ) -> Result<u128, ConcreteError> {
        check_width(expected_width)?;
        let (value, inner_width) = self.eval_bv_any(inner)?;
        if expected_width < inner_width {
            return Err(ConcreteError::InvalidWidth(expected_width));
        }
        let extension_bits = expected_width - inner_width;
        if amount_or_width != expected_width && amount_or_width != extension_bits {
            return Err(ConcreteError::SortMismatch("bit-vector extension width"));
        }
        let extended = if sign_extend && sign_bit(value, inner_width) {
            value | (mask(expected_width) ^ mask(inner_width))
        } else {
            value
        };
        Ok(truncate(extended, expected_width))
    }

    fn is_concrete_memory_array(&self, formula: &Formula) -> bool {
        matches!(formula, Formula::Var(name, _) if name == "MEM")
            || matches!(formula, Formula::SymVar(sym, _) if sym.as_str() == "MEM")
    }
}

/// Evaluate an AArch64/x86 condition against concrete flags.
#[must_use]
pub fn eval_condition(flags: ConcreteFlags, condition: Condition) -> bool {
    match condition {
        Condition::Eq => flags.z,
        Condition::Ne => !flags.z,
        Condition::Cs => flags.c,
        Condition::Cc => !flags.c,
        Condition::Mi => flags.n,
        Condition::Pl => !flags.n,
        Condition::Vs => flags.v,
        Condition::Vc => !flags.v,
        Condition::Hi => flags.c && !flags.z,
        Condition::Ls => !flags.c || flags.z,
        Condition::Ge => flags.n == flags.v,
        Condition::Lt => flags.n != flags.v,
        Condition::Gt => !flags.z && flags.n == flags.v,
        Condition::Le => flags.z || flags.n != flags.v,
        Condition::Al | Condition::Nv => true,
        _ => false,
    }
}

fn check_width(width: u32) -> Result<(), ConcreteError> {
    if (1..=128).contains(&width) { Ok(()) } else { Err(ConcreteError::InvalidWidth(width)) }
}

fn memory_bit_width(width_bytes: u32) -> Result<u32, ConcreteError> {
    let Some(width) = width_bytes.checked_mul(8) else {
        return Err(ConcreteError::UnsupportedMemoryWidth(width_bytes));
    };
    if matches!(width_bytes, 1 | 2 | 4 | 8 | 16) && width <= 128 {
        Ok(width)
    } else {
        Err(ConcreteError::UnsupportedMemoryWidth(width_bytes))
    }
}

fn extension_target_width(inner_width: u32, amount_or_width: u32) -> Result<u32, ConcreteError> {
    let target_width = if amount_or_width <= inner_width || !is_standard_bv_width(amount_or_width) {
        inner_width
            .checked_add(amount_or_width)
            .ok_or(ConcreteError::InvalidWidth(amount_or_width))?
    } else {
        amount_or_width
    };
    if target_width < inner_width {
        return Err(ConcreteError::InvalidWidth(target_width));
    }
    check_width(target_width)?;
    Ok(target_width)
}

fn is_standard_bv_width(width: u32) -> bool {
    matches!(width, 1 | 8 | 16 | 32 | 64 | 128)
}

fn checked_byte_address(address: u64, offset: u32, width_bytes: u32) -> Result<u64, ConcreteError> {
    address
        .checked_add(u64::from(offset))
        .ok_or(ConcreteError::MemoryAddressOverflow { address, width_bytes })
}

fn mask(width: u32) -> u128 {
    if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
}

fn truncate(value: u128, width: u32) -> u128 {
    value & mask(width)
}

fn truncate_i128(value: i128, width: u32) -> u128 {
    truncate(value as u128, width)
}

fn sign_bit(value: u128, width: u32) -> bool {
    ((value >> (width - 1)) & 1) == 1
}

fn signed_to_i128(value: u128, width: u32) -> i128 {
    let value = truncate(value, width);
    if !sign_bit(value, width) || width == 128 {
        value as i128
    } else {
        (value as i128) - (1i128 << width)
    }
}

// Verifier-demo fixtures: these intentionally exercise overflow and bounds
// checks so the Trust verification pass has known-broken targets it can
// catch in tests and CI gating. Kept above `mod tests` so clippy does not
// flag them with `items_after_test_module`.
pub fn test_verify_overflow(a: u32, b: u32) -> u32 {
    a + b // This can definitely overflow.
}

pub fn test_verify_bounds(arr: &[u32], idx: usize) -> u32 {
    arr[idx] // This can definitely go out of bounds.
}

// Mirror fixture for the verifier — contract-clause form. The
// `contract_requires` syntax requires `#![feature(contracts_internals)]`
// at the crate root (see lib.rs). Kept above the test module to avoid
// `items_after_test_module`.
pub fn trigger_trust_verifier_overflow_again(a: usize, b: usize) -> usize
contract_requires { a <= b }
{
    a + (b - a) / 2
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort};

    use super::*;
    use crate::effect::{Aarch64AtomicAccessKind, Aarch64AtomicOrdering};

    fn bv(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }

    #[test]
    fn replays_register_and_pc_effects() {
        let mut state = ConcreteState::new();
        state.gpr[1] = 40;
        state.gpr[2] = 2;
        state.pc = 0x1000;

        state
            .apply_effects(&[
                Effect::RegWrite {
                    index: 0,
                    width: 64,
                    value: Formula::BvAdd(
                        Box::new(Formula::Var("X1".into(), Sort::BitVec(64))),
                        Box::new(Formula::Var("X2".into(), Sort::BitVec(64))),
                        64,
                    ),
                },
                Effect::PcUpdate {
                    value: Formula::BvAdd(
                        Box::new(Formula::Var("PC".into(), Sort::BitVec(64))),
                        Box::new(bv(4, 64)),
                        64,
                    ),
                },
            ])
            .expect("replay");

        assert_eq!(state.gpr[0], 42);
        assert_eq!(state.pc, 0x1004);
    }

    #[test]
    fn updates_flags_from_formula_results() {
        let mut state = ConcreteState::new();
        let result = Formula::BvSub(Box::new(bv(1, 64)), Box::new(bv(1, 64)), 64);

        state
            .apply_effect(&Effect::FlagUpdate {
                n: Formula::Eq(
                    Box::new(Formula::BvExtract {
                        inner: Box::new(result.clone()),
                        high: 63,
                        low: 63,
                    }),
                    Box::new(bv(1, 1)),
                ),
                z: Formula::Eq(Box::new(result), Box::new(bv(0, 64))),
                c: Formula::Bool(true),
                v: Formula::Bool(false),
            })
            .expect("flags");

        assert_eq!(state.flags, ConcreteFlags { n: false, z: true, c: true, v: false });
    }

    #[test]
    fn replays_little_endian_memory_effects() {
        let mut state = ConcreteState::new();

        state
            .apply_effect(&Effect::MemWrite {
                address: bv(0x1000, 64),
                value: bv(0x1122_3344_5566_7788, 64),
                width_bytes: 8,
            })
            .expect("store");

        assert_eq!(state.load_memory_le(0x1000, 8).expect("load"), 0x1122_3344_5566_7788);
        assert_eq!(
            state
                .eval_bv(
                    &Formula::Select(
                        Box::new(Formula::Var(
                            "MEM".into(),
                            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
                        )),
                        Box::new(bv(0x1000, 64)),
                    ),
                    8,
                )
                .expect("select"),
            0x88
        );
    }

    #[test]
    fn effect_with_eval_state_uses_instruction_pre_state_for_sp_relative_store() {
        let mut pre_state = ConcreteState::new();
        pre_state.sp = 0x2000;
        pre_state.gpr[0] = 0x1122_3344_5566_7788;
        let mut state = pre_state.clone();
        let new_sp = Formula::BvSub(
            Box::new(Formula::Var("SP".into(), Sort::BitVec(64))),
            Box::new(bv(8, 64)),
            64,
        );

        state
            .apply_effect_with_eval_state(&pre_state, &Effect::SpWrite { value: new_sp.clone() })
            .expect("sp write");
        state
            .apply_effect_with_eval_state(
                &pre_state,
                &Effect::MemWrite {
                    address: new_sp,
                    value: Formula::Var("X0".into(), Sort::BitVec(64)),
                    width_bytes: 8,
                },
            )
            .expect("stack store");

        assert_eq!(state.sp, 0x1ff8);
        assert_eq!(state.load_memory_le(0x1ff8, 8).expect("load"), 0x1122_3344_5566_7788);
        assert!(!state.memory.contains_key(&0x1ff0));
    }

    #[test]
    fn rejects_uninitialized_memory_reads() {
        let mut state = ConcreteState::new();
        let err = state
            .apply_effect(&Effect::MemRead { address: bv(0x2000, 64), width_bytes: 8 })
            .expect_err("uninitialized memory must fail closed");

        assert_eq!(err, ConcreteError::UninitializedMemory { address: 0x2000 });
    }

    #[test]
    fn aarch64_atomic_access_metadata_is_replay_state_neutral() {
        let mut state = ConcreteState::new();
        state.gpr[0] = 0x1122_3344_5566_7788;
        state.gpr[1] = 0x2000;
        state.pc = 0x1000;

        let before = state.clone();
        state
            .apply_effect(&Effect::Aarch64AtomicAccess {
                kind: Aarch64AtomicAccessKind::Load,
                ordering: Aarch64AtomicOrdering::Acquire,
                address: Formula::Var("X1".into(), Sort::BitVec(64)),
                width_bytes: 8,
                exclusive: false,
            })
            .expect("atomic access metadata should be replay state neutral");

        assert_eq!(state, before);
    }

    #[test]
    fn rejects_unknown_formula_variables() {
        let state = ConcreteState::new();
        let err = state
            .eval_bv(&Formula::Var("RAX".into(), Sort::BitVec(64)), 64)
            .expect_err("unknown vars fail closed");

        assert_eq!(err, ConcreteError::UnknownVariable("RAX".into()));
    }

    #[test]
    fn applies_conditional_branch_fallthrough() {
        let mut state = ConcreteState::new();
        state.pc = 0x1000;
        state.flags.z = false;

        state
            .apply_effect(&Effect::ConditionalBranch {
                condition: Condition::Eq,
                target: bv(0x2000, 64),
                fallthrough: bv(0x1004, 64),
            })
            .expect("conditional branch");

        assert_eq!(state.pc, 0x1004);
    }

    #[test]
    fn applies_conditional_branch_taken() {
        let mut state = ConcreteState::new();
        state.pc = 0x1000;
        state.flags.z = true;

        state
            .apply_effect(&Effect::ConditionalBranch {
                condition: Condition::Eq,
                target: bv(0x2000, 64),
                fallthrough: bv(0x1004, 64),
            })
            .expect("conditional branch");

        assert_eq!(state.pc, 0x2000);
    }

    #[test]
    fn rejects_control_flow_effects() {
        let mut state = ConcreteState::new();
        let err = state
            .apply_effect(&Effect::Branch { target: bv(0x2000, 64) })
            .expect_err("branches are outside straight-line replay");

        assert_eq!(err, ConcreteError::UnsupportedEffect("control flow"));
    }
}

/// The concrete ISA oracle treats `Aarch64SyncBoundary` and a NON-exclusive
/// `Aarch64AtomicAccess` as no-ops. That is a claim about what those effects
/// mean for a single-threaded scalar interpreter, and it depends on a
/// precondition — that no EXCLUSIVE access ever reaches the oracle — which these
/// tests measure rather than assume.
#[cfg(test)]
mod sync_and_atomic_oracle_contract_tests {
    use trust_disasm::decode_aarch64;

    use crate::aarch64::Aarch64Semantics;
    use crate::effect::Effect;
    use crate::semantics::Semantics;
    use crate::state::MachineState;

    fn effects_of(enc: u32) -> Result<Vec<Effect>, crate::error::SemError> {
        let insn = decode_aarch64(&enc.to_le_bytes(), 0x1000).expect("decode");
        Aarch64Semantics.effects(&MachineState::symbolic(), &insn)
    }

    /// The precondition behind the no-op: `Aarch64AtomicAccess` is only ever
    /// produced with `exclusive: false`, because every exclusive instruction is
    /// refused before any effect is built.
    ///
    /// If this ever fails, the no-op in `ConcreteState::apply_effect` is no
    /// longer sound — an exclusive access reserves/checks the monitor and STXR
    /// writes a status register that no adjacent effect carries.
    #[test]
    fn no_exclusive_atomic_access_effect_is_reachable() {
        // Assembler-derived (`clang --target=aarch64-none-elf` + `objdump -d`):
        //   885f7c20  ldxr  w0, [x1]        8800fc21  stlxr w0, w1, [x1]
        //   885ffc20  ldaxr w0, [x1]        88007c21  stxr  w0, w1, [x1]
        for enc in [0x885F_7C20u32, 0x885F_FC20, 0x8800_FC21, 0x8800_7C21] {
            let err = effects_of(enc)
                .expect_err("an exclusive access must fail closed before producing effects");
            assert!(
                matches!(err, crate::error::SemError::UnsupportedAtomic { .. }),
                "{enc:#010x} should be UnsupportedAtomic, got {err:?}"
            );
        }

        // And the two opcodes that DO produce the effect produce the
        // non-exclusive form. ldar w0,[x1] = 88dffc20, stlr w0,[x1] = 889ffc20.
        for enc in [0x88DF_FC20u32, 0x889F_FC20] {
            let effects = effects_of(enc).unwrap_or_else(|e| panic!("{enc:#010x}: {e:?}"));
            let atomic = effects
                .iter()
                .find_map(|e| match e {
                    Effect::Aarch64AtomicAccess { exclusive, .. } => Some(*exclusive),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("{enc:#010x} produced no atomic-access effect"));
            assert!(!atomic, "{enc:#010x} produced an EXCLUSIVE atomic access");
        }
    }

    /// The other half of the no-op's justification: the acquire/release
    /// instructions carry their DATA plane in separate effects, so ignoring the
    /// ordering metadata drops nothing a scalar oracle could observe.
    #[test]
    fn acquire_release_carry_their_data_plane_in_separate_effects() {
        let ldar = effects_of(0x88DF_FC20).expect("ldar");
        assert!(
            ldar.iter().any(|e| matches!(e, Effect::MemRead { .. }))
                && ldar.iter().any(|e| matches!(e, Effect::RegWrite { .. })),
            "LDAR must emit its load data plane as MemRead + RegWrite: {ldar:?}"
        );

        let stlr = effects_of(0x889F_FC20).expect("stlr");
        assert!(
            stlr.iter().any(|e| matches!(e, Effect::MemWrite { .. })),
            "STLR must emit its store data plane as MemWrite: {stlr:?}"
        );
    }

    /// A barrier's producers emit ONLY the boundary plus the PC advance — there
    /// is no data plane for the oracle's `Ok(())` to be dropping.
    #[test]
    fn barriers_have_no_data_plane() {
        // Assembler-derived: dmb ish = d5033bbf, dsb ish = d5033b9f,
        // isb = d5033fdf, clrex = d5033f5f.
        for enc in [0xD503_3BBFu32, 0xD503_3B9F, 0xD503_3FDF, 0xD503_3F5F] {
            let effects = effects_of(enc).unwrap_or_else(|e| panic!("{enc:#010x}: {e:?}"));
            assert!(
                effects.iter().all(|e| matches!(
                    e,
                    Effect::Aarch64SyncBoundary { .. } | Effect::PcUpdate { .. }
                )),
                "{enc:#010x} emitted more than a boundary and a PC advance: {effects:?}"
            );
        }
    }
}

#[cfg(test)]
mod f16_primitive_tests {
    use super::*;

    /// The whole f16 space, round-tripped: widening is exact and every f16
    /// value is exactly representable in f32, so `pack(unpack(h)) == h` — with
    /// ONE principled exception: a signaling NaN comes back with its quiet bit
    /// set, which is exactly what AArch64 does on any conversion or arithmetic
    /// use of it (FPCR.DN=0 propagates the payload and forces quiet).
    ///
    /// 65,536 cases; exhaustive, not sampled.
    #[test]
    fn every_f16_round_trips_exactly() {
        for h in 0..=u16::MAX {
            let widened = f16_bits_to_f32(h);
            let back = f32_to_f16_bits(widened);
            let exp = (h >> 10) & 0x1F;
            let frac = h & 0x3FF;
            let is_snan = exp == 0x1F && frac != 0 && (frac & 0x200) == 0;
            let expected = if is_snan { h | 0x200 } else { h };
            assert_eq!(
                back,
                expected,
                "f16 {h:#06x} widened to {widened} ({:#010x}) and came back {back:#06x}",
                widened.to_bits()
            );
        }
    }

    /// Widening preserves VALUE for every finite f16: check a few exact
    /// anchors against hand-computed constants, including subnormals and the
    /// extremes.
    #[test]
    fn f16_widening_hits_known_values() {
        let cases: &[(u16, f32)] = &[
            (0x3C00, 1.0),
            (0xBC00, -1.0),
            (0x3555, 0.333_251_95),   // closest f16 to 1/3
            (0x0001, 5.960_464_5e-8), // smallest subnormal, 2^-24
            (0x03FF, 6.097_555_1e-5), // largest subnormal
            (0x0400, 6.103_515_6e-5), // smallest normal, 2^-14
            (0x7BFF, 65504.0),        // largest finite
            (0x0000, 0.0),
            (0x8000, -0.0),
        ];
        for (h, expected) in cases {
            let got = f16_bits_to_f32(*h);
            assert_eq!(got, *expected, "{h:#06x} must widen to {expected}");
        }
        assert!(f16_bits_to_f32(0x7C00).is_infinite());
        assert!(f16_bits_to_f32(0x7E00).is_nan());
    }

    /// Narrowing rounds ties to even and saturates to infinity — the corners a
    /// wrong shift or bias silently breaks.
    #[test]
    fn f16_narrowing_rounds_to_nearest_even() {
        // 1.0 + 2^-11 is exactly halfway between 1.0 and the next f16; RNE
        // picks the EVEN mantissa, i.e. 1.0.
        assert_eq!(f32_to_f16_bits(1.0 + f32::powi(2.0, -11)), 0x3C00);
        // Three quarters of the way rounds up.
        assert_eq!(f32_to_f16_bits(1.0 + 3.0 * f32::powi(2.0, -12)), 0x3C01);
        // Just past the largest finite f16 rounds to infinity; just below the
        // halfway point stays finite.
        assert_eq!(f32_to_f16_bits(65520.0), 0x7C00, "halfway to 65536 ties to even = inf");
        assert_eq!(f32_to_f16_bits(65519.9), 0x7BFF);
        assert_eq!(f32_to_f16_bits(-65520.0), 0xFC00);
        // Deep underflow flushes to signed zero under RNE.
        assert_eq!(f32_to_f16_bits(1.0e-10), 0x0000);
        assert_eq!(f32_to_f16_bits(-1.0e-10), 0x8000);
    }
}
