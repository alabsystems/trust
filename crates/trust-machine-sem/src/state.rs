// trust-machine-sem: Machine state representation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{Formula, Sort};

use crate::effect::Effect;

/// Symbolic machine state: registers, flags, memory, and program counter.
///
/// All components are represented as SMT-level `Formula` values, enabling
/// symbolic reasoning about instruction effects.
#[derive(Debug, Clone)]
pub struct MachineState {
    /// General-purpose registers X0-X30, each a 64-bit bitvector.
    pub gpr: [Formula; 31],
    /// SIMD/FP registers V0-V31, each a 128-bit bitvector.
    /// Scalar FP operations (S/D) use the low 32/64 bits; upper bits are zeroed.
    pub fpr: [Formula; 32],
    /// Stack pointer (SP), 64-bit bitvector.
    pub sp: Formula,
    /// Program counter (PC), 64-bit bitvector.
    pub pc: Formula,
    /// NZCV condition flags (individual booleans).
    pub flags: Flags,
    /// Memory as an SMT array: `(Array BitVec64 BitVec8)`.
    pub memory: Formula,
}

/// The four AArch64 condition flags.
#[derive(Debug, Clone)]
pub struct Flags {
    /// Negative flag.
    pub n: Formula,
    /// Zero flag.
    pub z: Formula,
    /// Carry flag.
    pub c: Formula,
    /// Overflow flag.
    pub v: Formula,
}

impl Flags {
    /// Create symbolic flag variables with a given prefix (e.g. "pre" or "post").
    #[must_use]
    pub fn symbolic(prefix: &str) -> Self {
        Self {
            n: Formula::Var(format!("{prefix}_N"), Sort::Bool),
            z: Formula::Var(format!("{prefix}_Z"), Sort::Bool),
            c: Formula::Var(format!("{prefix}_C"), Sort::Bool),
            v: Formula::Var(format!("{prefix}_V"), Sort::Bool),
        }
    }
}

impl MachineState {
    /// Create a fully symbolic initial state with named variables.
    ///
    /// Registers are `X0`..`X30`, FP registers are `V0`..`V31`,
    /// SP is `SP`, PC is `PC`, flags are `N/Z/C/V`, memory is `MEM`.
    #[must_use]
    pub fn symbolic() -> Self {
        let bv64 = Sort::BitVec(64);
        let bv128 = Sort::BitVec(128);
        let gpr = core::array::from_fn(|i| Formula::Var(format!("X{i}"), bv64.clone()));
        let fpr = core::array::from_fn(|i| Formula::Var(format!("V{i}"), bv128.clone()));
        Self {
            gpr,
            fpr,
            sp: Formula::Var("SP".into(), bv64.clone()),
            pc: Formula::Var("PC".into(), bv64),
            flags: Flags::symbolic(""),
            memory: Formula::Var(
                "MEM".into(),
                Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
            ),
        }
    }

    /// Read a GPR by index (0-30). Returns the zero constant for index 31 at
    /// the given width.
    #[must_use]
    pub fn read_gpr(&self, index: u8, width: u32) -> Formula {
        if index >= 31 {
            // Zero register
            return Formula::BitVec { value: 0, width };
        }
        let full = self.gpr[index as usize].clone();
        if width == 64 {
            full
        } else {
            // Truncate to lower `width` bits.
            Formula::BvExtract { inner: Box::new(full), high: width - 1, low: 0 }
        }
    }

    /// Read the stack pointer at the given width.
    #[must_use]
    pub fn read_sp(&self, width: u32) -> Formula {
        if width == 64 {
            self.sp.clone()
        } else {
            Formula::BvExtract { inner: Box::new(self.sp.clone()), high: width - 1, low: 0 }
        }
    }

    /// Read a SIMD/FP register by index (0-31) at the given width (32/64/128).
    ///
    /// The full register is 128 bits (Q). Scalar accesses (S=32, D=64) extract
    /// the low bits.
    #[must_use]
    pub fn read_fpr(&self, index: u8, width: u32) -> Formula {
        let full = self.fpr[index as usize].clone();
        if width >= 128 {
            full
        } else {
            Formula::BvExtract { inner: Box::new(full), high: width - 1, low: 0 }
        }
    }

    /// Apply a single instruction [`Effect`] to this state SYMBOLICALLY,
    /// composing `Formula`s into the post-state (never evaluating to concretes).
    ///
    /// This is the symbolic counterpart of [`crate::ConcreteState::apply_effect`]:
    /// instead of evaluating each effect against concrete register bindings, it
    /// threads the effect's `Formula` value into the corresponding state slot, so
    /// after running a decoded instruction sequence the result register holds a
    /// full-program symbolic expression over the initial (symbolic) inputs. That
    /// expression is what gets discharged against the IR semantics by an SMT
    /// solver — extending route-(a) validation from finite exhaustive execution
    /// to all inputs of an infinite domain.
    ///
    /// Fail-closed: effects whose symbolic semantics are not modeled here (calls,
    /// condition-keyed branches, atomics, sync boundaries) return
    /// `Err(ApplyEffectError::Unmodeled)` rather than silently producing an
    /// unsound post-state — so a proof built on this transition only ever covers
    /// instruction sequences it fully models.
    pub fn apply_effect(&mut self, effect: &Effect) -> Result<(), ApplyEffectError> {
        match effect {
            Effect::RegWrite { index, width, value } => {
                if *index < 31 {
                    // AArch64: a 32-bit (W) write zero-extends into the 64-bit X reg.
                    self.gpr[*index as usize] = widen_zero(value.clone(), *width, 64)?;
                }
            }
            Effect::SpWrite { value } => self.sp = value.clone(),
            Effect::FpRegWrite { index, width, value } => {
                self.fpr[*index as usize] = widen_zero(value.clone(), *width, 128)?;
            }
            Effect::MemWrite { address, value, width_bytes } => {
                self.memory = store_bytes_le(self.memory.clone(), address, value, *width_bytes);
            }
            // A pure read does not change architectural state; the loaded value
            // reaches a register via the paired RegWrite the semantics also emits.
            Effect::MemRead { .. } => {}
            Effect::FlagUpdate { n, z, c, v } => {
                self.flags =
                    Flags { n: n.clone(), z: z.clone(), c: c.clone(), v: v.clone() };
            }
            Effect::Branch { target } | Effect::Return { target } => self.pc = target.clone(),
            Effect::PcUpdate { value } => self.pc = value.clone(),
            other => return Err(ApplyEffectError::Unmodeled(effect_name(other))),
        }
        Ok(())
    }

    /// Apply a sequence of effects in program order, threading the symbolic state.
    pub fn apply_effects(&mut self, effects: &[Effect]) -> Result<(), ApplyEffectError> {
        for e in effects {
            self.apply_effect(e)?;
        }
        Ok(())
    }
}

/// Zero-extend `value` (a `from`-bit bitvector) to `to` bits (AArch64 W→X form).
fn widen_zero(value: Formula, from: u32, to: u32) -> Result<Formula, ApplyEffectError> {
    use core::cmp::Ordering;
    match from.cmp(&to) {
        Ordering::Equal => Ok(value),
        Ordering::Less => Ok(Formula::BvZeroExt(Box::new(value), to - from)),
        Ordering::Greater => Err(ApplyEffectError::BadWidth { from, to }),
    }
}

/// Store the low `width_bytes` bytes of `value` into the `memory` array
/// `Formula` at `address`, little-endian, returning the updated array.
fn store_bytes_le(memory: Formula, address: &Formula, value: &Formula, width_bytes: u32) -> Formula {
    let mut mem = memory;
    for i in 0..width_bytes {
        let byte =
            Formula::BvExtract { inner: Box::new(value.clone()), high: 8 * i + 7, low: 8 * i };
        let addr = if i == 0 {
            address.clone()
        } else {
            Formula::BvAdd(
                Box::new(address.clone()),
                Box::new(Formula::BitVec { value: i128::from(i), width: 64 }),
                64,
            )
        };
        mem = Formula::Store(Box::new(mem), Box::new(addr), Box::new(byte));
    }
    mem
}

fn effect_name(effect: &Effect) -> &'static str {
    match effect {
        Effect::Call { .. } => "Call",
        Effect::ConditionalBranch { .. } => "ConditionalBranch",
        Effect::Aarch64SyncBoundary { .. } => "Aarch64SyncBoundary",
        Effect::Aarch64AtomicAccess { .. } => "Aarch64AtomicAccess",
        _ => "unmodeled effect",
    }
}

/// Error from symbolically applying an [`Effect`] to a [`MachineState`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ApplyEffectError {
    /// The effect's symbolic semantics are not modeled (fail-closed).
    Unmodeled(&'static str),
    /// A register-write width could not be zero-extended to the register width.
    BadWidth {
        /// Source value width in bits.
        from: u32,
        /// Target register width in bits.
        to: u32,
    },
}

impl core::fmt::Display for ApplyEffectError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Unmodeled(what) => write!(f, "unmodeled symbolic effect: {what}"),
            Self::BadWidth { from, to } => {
                write!(f, "cannot zero-extend {from}-bit value to {to} bits")
            }
        }
    }
}

impl std::error::Error for ApplyEffectError {}

#[cfg(test)]
mod symbolic_apply_tests {
    use super::*;

    // Symbolic model of `add w0, w0, w1; ret` for i32 add(a, b): the post-state
    // X0 must hold zero-extend(W0 + W1), and its low 32 bits the exact 32-bit sum
    // — composed purely as formulas, threading state with no concretes.
    #[test]
    fn add_w0_w1_then_ret_composes_to_sum() {
        let mut st = MachineState::symbolic();
        let a = st.read_gpr(0, 32);
        let b = st.read_gpr(1, 32);
        let sum32 = Formula::BvAdd(Box::new(a), Box::new(b), 32);

        st.apply_effect(&Effect::RegWrite { index: 0, width: 32, value: sum32.clone() })
            .unwrap();
        let x30 = st.read_gpr(30, 64);
        st.apply_effect(&Effect::Return { target: x30.clone() }).unwrap();

        assert_eq!(st.gpr[0], Formula::BvZeroExt(Box::new(sum32.clone()), 32));
        assert_eq!(
            st.read_gpr(0, 32),
            Formula::BvExtract {
                inner: Box::new(Formula::BvZeroExt(Box::new(sum32), 32)),
                high: 31,
                low: 0,
            }
        );
        assert_eq!(st.pc, x30, "pc must thread to the return target");
    }

    #[test]
    fn unmodeled_effect_fails_closed() {
        let mut st = MachineState::symbolic();
        let err = st.apply_effect(&Effect::Call {
            target: Formula::BitVec { value: 0, width: 64 },
            return_addr: Formula::BitVec { value: 0, width: 64 },
        });
        assert!(matches!(err, Err(ApplyEffectError::Unmodeled(_))));
    }

    #[test]
    fn mem_write_threads_store_into_memory_array() {
        let mut st = MachineState::symbolic();
        let before = st.memory.clone();
        st.apply_effect(&Effect::MemWrite {
            address: st.read_sp(64),
            value: st.read_gpr(0, 64),
            width_bytes: 8,
        })
        .unwrap();
        assert_ne!(st.memory, before);
        assert!(matches!(st.memory, Formula::Store(..)));
    }
}
