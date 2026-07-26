// trust-machine-sem: bounded concrete replay
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use trust_disasm::operand::Condition;
use trust_types::Formula;

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
    /// Initialized byte-addressed memory.
    pub memory: BTreeMap<u64, u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConcreteValue {
    Bool(bool),
    Bv { value: u128, width: u32 },
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
            memory: BTreeMap::new(),
        }
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
            Effect::FpRegWrite { .. } => Err(ConcreteError::UnsupportedEffect("floating point")),
            Effect::Aarch64SyncBoundary { .. } => Ok(()),
            Effect::Aarch64AtomicAccess { .. } => Ok(()),
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
            Effect::FpRegWrite { .. } => Err(ConcreteError::UnsupportedEffect("floating point")),
            Effect::Aarch64SyncBoundary { .. } => Ok(()),
            Effect::Aarch64AtomicAccess { .. } => Ok(()),
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

        match name {
            "SP" => Ok(ConcreteValue::Bv { value: u128::from(self.sp), width: 64 }),
            "PC" => Ok(ConcreteValue::Bv { value: u128::from(self.pc), width: 64 }),
            "N" | "_N" => Ok(ConcreteValue::Bool(self.flags.n)),
            "Z" | "_Z" => Ok(ConcreteValue::Bool(self.flags.z)),
            "C" | "_C" => Ok(ConcreteValue::Bool(self.flags.c)),
            "V" | "_V" => Ok(ConcreteValue::Bool(self.flags.v)),
            _ => Err(ConcreteError::UnknownVariable(name.to_owned())),
        }
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

    use crate::effect::{Aarch64AtomicAccessKind, Aarch64AtomicOrdering};

    use super::*;

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
