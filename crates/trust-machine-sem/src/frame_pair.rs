//! Exact binding of the observed Darwin FP/LR pair to canonical memory effects.
//!
//! The input is raw instruction bytes, never a caller-built decoded summary.
//! The existing decoder and Aarch64Semantics produce the complete effect list;
//! every effect must agree with the two-transfer little-endian operation used
//! by SemR.MemoryEmbedding.FramePair. This binds a single instruction's model,
//! not object membership, allocation ownership, a call rely or a proof grade.
//!
//! `pc` is the address supplied to the decoder. The symbolic `pre.pc` is only
//! sort-checked, and the resulting PC effect is `pre.pc + 4`. A later execution
//! witness must establish their semantic equality on the actual path, membership
//! of these four bytes in the bound executable object/function at that address,
//! and valid instruction-fetch alignment. It must also relate the actual SP and
//! memory to the checked placed frame, including alignment and nonwrapping
//! bounds. This API neither assumes those facts nor requires syntactic equality
//! of a symbolic PC with the supplied decoder address.

use trust_disasm::operand::MemoryOperand;
use trust_disasm::{ControlFlow, Opcode, Operand, Register, decode_aarch64};
use trust_types::{Formula, Sort, check_formula_sort};

use crate::{Aarch64Semantics, Effect, MachineState, Semantics};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairRole {
    Save,
    Restore,
}

/// A complete checked word/effect binding for the supplied bytes and pre-state.
/// Its constructor recomputes decoding/effects; it accepts no claimed effect
/// list. The SemR theorem still needs a checked placed allocation and the
/// canonical/formula-memory representation to be instantiated. Execution-PC,
/// aligned object membership and actual SP/frame custody remain separate.
pub struct CheckedPairEffects<'a> {
    bytes: [u8; 4],
    pc: u64,
    role: PairRole,
    pre: &'a MachineState,
    post: MachineState,
    effects: Vec<Effect>,
    address: Formula,
}

impl CheckedPairEffects<'_> {
    pub fn bytes(&self) -> [u8; 4] {
        self.bytes
    }
    /// Caller-supplied decoder address, not a proved execution location.
    pub fn pc(&self) -> u64 {
        self.pc
    }
    pub fn role(&self) -> PairRole {
        self.role
    }
    pub fn pre(&self) -> &MachineState {
        self.pre
    }
    pub fn post(&self) -> &MachineState {
        &self.post
    }
    pub fn effects(&self) -> &[Effect] {
        &self.effects
    }
    pub fn first_address(&self) -> &Formula {
        &self.address
    }
}

fn bv(value: i128) -> Formula {
    Formula::BitVec { value, width: 64 }
}
fn add(value: &Formula, offset: i128) -> Formula {
    Formula::BvAdd(Box::new(value.clone()), Box::new(bv(offset)), 64)
}

// This is the exact eight-byte little-endian value in the canonical pair
// effect relation, checked against the independently produced effect formula.
fn load_word(memory: &Formula, address: &Formula) -> Formula {
    let byte = |index| {
        let at = if index == 0 { address.clone() } else { add(address, index) };
        Formula::BvZeroExt(Box::new(Formula::Select(Box::new(memory.clone()), Box::new(at))), 56)
    };
    let mut result = byte(0);
    for index in 1..8 {
        let lane = Formula::BvShl(Box::new(byte(index)), Box::new(bv(index * 8)), 64);
        result = Formula::BvOr(Box::new(result), Box::new(lane), 64);
    }
    result
}

fn check_effects(
    role: PairRole,
    pre: &MachineState,
    effects: &[Effect],
) -> Result<Formula, String> {
    let address = match role {
        PairRole::Save => add(&pre.sp, -16),
        PairRole::Restore => pre.sp.clone(),
    };
    let second = add(&address, 8);
    let writeback = match role {
        PairRole::Save => address.clone(),
        PairRole::Restore => add(&pre.sp, 16),
    };
    let mut expected = match role {
        PairRole::Save => vec![
            Effect::MemWrite {
                address: address.clone(),
                value: pre.gpr[29].clone(),
                width_bytes: 8,
            },
            Effect::MemWrite { address: second, value: pre.gpr[30].clone(), width_bytes: 8 },
        ],
        PairRole::Restore => vec![
            Effect::MemRead { address: address.clone(), width_bytes: 8 },
            Effect::MemRead { address: second.clone(), width_bytes: 8 },
            Effect::RegWrite { index: 29, width: 64, value: load_word(&pre.memory, &address) },
            Effect::RegWrite { index: 30, width: 64, value: load_word(&pre.memory, &second) },
        ],
    };
    expected.push(Effect::SpWrite { value: writeback });
    expected.push(Effect::PcUpdate { value: add(&pre.pc, 4) });
    if effects != expected {
        return Err("complete pair effects differ from canonical FP/LR memory relation".into());
    }
    Ok(address)
}

/// Check the decoded word's complete effects for this supplied pre-state.
/// No execution-PC correspondence, object membership, fetch alignment or
/// SP/allocation custody is established; see the module's required witnesses.
pub fn bind<'a>(
    bytes: [u8; 4],
    pc: u64,
    pre: &'a MachineState,
) -> Result<CheckedPairEffects<'a>, String> {
    let role = match u32::from_le_bytes(bytes) {
        0xa9bf_7bfd => PairRole::Save,
        0xa8c1_7bfd => PairRole::Restore,
        _ => return Err("not an observed FP/LR16 pre-index save or post-index restore word".into()),
    };
    let instruction = decode_aarch64(&bytes, pc).map_err(|error| format!("decode: {error:?}"))?;
    let opcode = match role {
        PairRole::Save => Opcode::Stp,
        PairRole::Restore => Opcode::Ldp,
    };
    let memory = match role {
        PairRole::Save => MemoryOperand::PreIndex { base: Register::sp(true), offset: -16 },
        PairRole::Restore => MemoryOperand::PostIndex { base: Register::sp(true), offset: 16 },
    };
    if instruction.size != 4
        || instruction.address != pc
        || instruction.bytes != bytes
        || instruction.opcode != opcode
        || instruction.flow != ControlFlow::Fallthrough
        || instruction.operand_count() != 3
        || instruction.operand(0) != Some(&Operand::Reg(Register::gpr(29, true)))
        || instruction.operand(1) != Some(&Operand::Reg(Register::gpr(30, true)))
        || instruction.operand(2) != Some(&Operand::Mem(memory))
    {
        return Err(
            "raw word does not decode to the complete required operands/address mode".into()
        );
    }
    let memory_sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
    for (value, expected) in [
        (&pre.sp, Sort::BitVec(64)),
        (&pre.pc, Sort::BitVec(64)),
        (&pre.gpr[29], Sort::BitVec(64)),
        (&pre.gpr[30], Sort::BitVec(64)),
        (&pre.memory, memory_sort),
    ] {
        if check_formula_sort(value).map_err(|error| format!("sort: {error:?}"))? != expected {
            return Err("pair entry state has the wrong complete value/address width".into());
        }
    }
    let effects = Aarch64Semantics
        .effects(pre, &instruction)
        .map_err(|error| format!("effects: {error:?}"))?;
    let address = check_effects(role, pre, &effects)?;
    let mut post = pre.clone();
    post.apply_effects(&effects).map_err(|error| format!("apply: {error:?}"))?;
    Ok(CheckedPairEffects { bytes, pc, role, pre, post, effects, address })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ConcreteState;

    #[test]
    fn actual_fp_lr_words_bind_complete_effects_and_all_saved_bits() {
        let pre = MachineState::symbolic();
        let save = bind(0xa9bf_7bfdu32.to_le_bytes(), 20, &pre).unwrap();
        assert_eq!(save.role(), PairRole::Save);
        assert_eq!(save.effects().len(), 4);
        let restore = bind(0xa8c1_7bfdu32.to_le_bytes(), 32, save.post()).unwrap();
        assert_eq!(restore.role(), PairRole::Restore);
        assert_eq!(restore.effects().len(), 6);
        for (fp, lr) in
            [(0, 0), (u64::MAX, 0), (0, u64::MAX), (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210)]
        {
            let mut state = ConcreteState::new();
            state.sp = 0x1000;
            state.gpr[29] = fp;
            state.gpr[30] = lr;
            let entry = state.clone();
            for effect in save.effects() {
                state.apply_effect_with_eval_state(&entry, effect).unwrap();
            }
            for index in 0..8 {
                assert_eq!(state.memory[&(0xff0 + index)], fp.to_le_bytes()[index as usize]);
                assert_eq!(state.memory[&(0xff8 + index)], lr.to_le_bytes()[index as usize]);
            }
            // Evaluate the LDP effects against its own pre-state symbols.
            let symbolic = MachineState::symbolic();
            let load = bind(0xa8c1_7bfdu32.to_le_bytes(), 32, &symbolic).unwrap();
            let before_load = state.clone();
            for effect in load.effects() {
                state.apply_effect_with_eval_state(&before_load, effect).unwrap();
            }
            assert_eq!((state.sp, state.gpr[29], state.gpr[30]), (0x1000, fp, lr));
        }
    }

    #[test]
    fn wrong_word_width_address_value_or_effect_census_cannot_bind() {
        let pre = MachineState::symbolic();
        for word in [0xa9be_7bfdu32, 0xa9bf_7bfc, 0xa93f_7bfd, 0x29bf_7bfd, 0xa8c2_7bfd] {
            assert!(bind(word.to_le_bytes(), 20, &pre).is_err());
        }
        let checked = bind(0xa9bf_7bfdu32.to_le_bytes(), 20, &pre).unwrap();
        for mutation in 0..5 {
            let mut effects = checked.effects().to_vec();
            match mutation {
                0 => effects.pop().map(|_| ()).unwrap(),
                1 => effects.push(Effect::MemRead { address: pre.sp.clone(), width_bytes: 8 }),
                2 => {
                    if let Effect::MemWrite { value, .. } = &mut effects[0] {
                        *value = pre.gpr[30].clone();
                    }
                }
                3 => {
                    if let Effect::MemWrite { address, .. } = &mut effects[1] {
                        *address = pre.sp.clone();
                    }
                }
                _ => {
                    if let Effect::MemWrite { width_bytes, .. } = &mut effects[0] {
                        *width_bytes = 4;
                    }
                }
            }
            assert!(check_effects(PairRole::Save, &pre, &effects).is_err());
        }
        let mut narrowed = pre.clone();
        narrowed.gpr[29] = Formula::BitVec { value: 1, width: 32 };
        assert!(bind(0xa9bf_7bfdu32.to_le_bytes(), 20, &narrowed).is_err());
    }
}
