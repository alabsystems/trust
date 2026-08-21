//! The MODEL side: what `X86_64Semantics` says an instruction does.
//!
//! Built out of the SHIPPING pieces — `decode_x86_64`,
//! `X86_64Semantics::effects`, `ConcreteState::apply_effect_with_eval_state` —
//! and adds nothing of its own. A differential whose model side is a
//! reimplementation tests the reimplementation.

use trust_disasm::decode_x86_64;
use trust_machine_sem::{
    ConcreteError, ConcreteState, Effect, MachineState, Semantics, X86_64Semantics,
};

use crate::ctx::{pattern_u64, scratch_range, Profile};
use crate::mutate::Mutation;

/// Why an instruction could not be compared. Never a verdict about it — only
/// about this harness's ability to speak about it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Skip {
    NotDecoded,
    NoEffects,
    UnsupportedEffect(String),
    EvalError(String),
}

pub struct Predicted {
    /// Decoder-order register file; slot 4 (rsp) carries the model's `sp`.
    pub gpr: [u64; 16],
    pub pc: u64,
    /// SF<<3 | ZF<<2 | CF<<1 | OF.
    pub flags: u8,
    /// Which flag bits the model actually CLAIMS. A flag whose formula is a
    /// deliberate per-instruction unknown (the shift CF/OF) is the model
    /// DECLINING to claim that bit — masked out of the comparison and counted,
    /// never compared against a value the model did not assert, and never
    /// allowed to skip the whole instruction (SF/ZF of a shift are real
    /// claims and stay compared).
    pub flags_mask: u8,
    pub mem: Vec<(u64, u64)>,
    pub mem_outside_window: bool,
    pub mem_read_outside_window: bool,
}

fn fill_pattern_word(state: &mut ConcreteState, address: u64) {
    let aligned = address & !7u64;
    let value = pattern_u64(aligned);
    for i in 0..8u64 {
        state.memory.insert(aligned + i, ((value >> (i * 8)) & 0xff) as u8);
    }
}

/// Run the model for one instruction at `pc`, starting from `profile`.
pub fn predict(
    bytes: &[u8],
    pc: u64,
    profile: &Profile,
    mutation: Mutation,
) -> Result<(usize, &'static str, Predicted), Skip> {
    let insn = decode_x86_64(bytes, pc).map_err(|_| Skip::NotDecoded)?;
    let len = usize::from(insn.size);
    let opcode: &'static str = opcode_name(insn.opcode);
    let sym = MachineState::symbolic();
    let effects =
        mutation.apply(X86_64Semantics.effects(&sym, &insn).map_err(|_| Skip::NoEffects)?);

    // Control-flow markers are annotations beside their PcUpdate; same guarded
    // drop as the AArch64 twin (whose blanket refusal of the marker silently
    // removed B/BL/BLR/BR from its oracle).
    let effects: Vec<Effect> = if effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. })) {
        effects
            .into_iter()
            .filter(|e| {
                !matches!(
                    e,
                    Effect::Branch { .. }
                        | Effect::Call { .. }
                        | Effect::Return { .. }
                        | Effect::ConditionalBranch { .. }
                )
            })
            .collect()
    } else {
        effects
    };

    let mut pre = ConcreteState::new();
    for i in 0..16 {
        if i != 4 {
            pre.gpr[i] = profile.gpr[i];
        }
    }
    pre.sp = profile.gpr[4];
    pre.pc = pc;
    pre.flags = trust_machine_sem::ConcreteFlags {
        n: profile.flags & 0b1000 != 0,
        z: profile.flags & 0b0100 != 0,
        c: profile.flags & 0b0010 != 0,
        v: profile.flags & 0b0001 != 0,
    };

    // FlagUpdate is applied BIT BY BIT so a deliberate unknown (the shift
    // CF/OF) masks ONE bit instead of skipping the instruction.
    let mut flags_mask = 0b1111u8;

    let mut post;
    let mut rounds = 0usize;
    let mut mem_read_outside_window = false;
    loop {
        post = pre.clone();
        flags_mask = 0b1111;
        // Fallthrough convention: no PcUpdate means the next instruction.
        post.pc = pc.wrapping_add(len as u64);
        let mut failure = None;
        for effect in &effects {
            if let Effect::FlagUpdate { n, z, c, v } = effect {
                let mut bit = |formula: &trust_types::Formula,
                               set: &mut dyn FnMut(&mut ConcreteState, bool),
                               mask: u8| match pre.eval_bool(formula) {
                    Ok(value) => {
                        set(&mut post, value);
                        Ok(())
                    }
                    Err(ConcreteError::UninitializedMemory { address }) => {
                        Err(ConcreteError::UninitializedMemory { address })
                    }
                    Err(_) => {
                        // The model declined this bit (an unknown flag var).
                        flags_mask &= !mask;
                        Ok(())
                    }
                };
                if let Err(e) = bit(n, &mut |s, b| s.flags.n = b, 0b1000)
                    .and_then(|()| bit(z, &mut |s, b| s.flags.z = b, 0b0100))
                    .and_then(|()| bit(c, &mut |s, b| s.flags.c = b, 0b0010))
                    .and_then(|()| bit(v, &mut |s, b| s.flags.v = b, 0b0001))
                {
                    failure = Some(e);
                    break;
                }
                continue;
            }
            if let Err(e) = post.apply_effect_with_eval_state(&pre, effect) {
                failure = Some(e);
                break;
            }
        }
        match failure {
            None => break,
            Some(ConcreteError::UninitializedMemory { address }) => {
                let (lo, hi) = scratch_range();
                if address < lo || address >= hi {
                    mem_read_outside_window = true;
                }
                fill_pattern_word(&mut pre, address);
                rounds += 1;
                if rounds > 256 {
                    return Err(Skip::EvalError("memory seeding did not converge".into()));
                }
            }
            Some(ConcreteError::UnsupportedEffect(what)) => {
                return Err(Skip::UnsupportedEffect(what.to_string()));
            }
            Some(other) => return Err(Skip::EvalError(format!("{other}"))),
        }
    }

    // Predicted memory diffs, promoted to 8-byte words.
    let (lo, hi) = scratch_range();
    let mut touched: Vec<u64> = Vec::new();
    for (&addr, &byte) in &post.memory {
        let aligned = addr & !7u64;
        let expect = ((pattern_u64(aligned) >> ((addr & 7) * 8)) & 0xff) as u8;
        if byte != expect && !touched.contains(&aligned) {
            touched.push(aligned);
        }
    }
    touched.sort_unstable();
    let mut mem = Vec::new();
    let mut mem_outside_window = false;
    for aligned in touched {
        if aligned < lo || aligned + 8 > hi {
            mem_outside_window = true;
            continue;
        }
        let mut value = pattern_u64(aligned);
        for i in 0..8u64 {
            if let Some(&b) = post.memory.get(&(aligned + i)) {
                value = (value & !(0xffu64 << (i * 8))) | (u64::from(b) << (i * 8));
            }
        }
        mem.push((aligned, value));
    }

    let mut gpr = [0u64; 16];
    for i in 0..16 {
        gpr[i] = if i == 4 { post.sp } else { post.gpr[i] };
    }
    let flags = u8::from(post.flags.n) << 3
        | u8::from(post.flags.z) << 2
        | u8::from(post.flags.c) << 1
        | u8::from(post.flags.v);

    Ok((
        len,
        opcode,
        Predicted { gpr, pc: post.pc, flags, flags_mask, mem, mem_outside_window, mem_read_outside_window },
    ))
}

fn opcode_name(op: trust_disasm::opcode::Opcode) -> &'static str {
    // Leak-free static naming via Debug is not available; use a small match on
    // the hot ones and a catch-all bucket. Family GRANULARITY only affects
    // reporting, never comparison.
    macro_rules! names {
        ($($v:ident),*) => {
            match op {
                $(trust_disasm::opcode::Opcode::$v => stringify!($v),)*
                _ => "Other",
            }
        };
    }
    names!(
        Mov, Add, Sub, Adc, Cmp, Test, And, Or, Xor, Shl, Shr, Sar, Lea, Push, Pop, Call,
        Jmp, Jcc, Ret, Nop, Inc, Dec, Neg, Not, Imul, Mul, Div, Idiv, Movsx, Movzx, Xchg, Setcc,
        Cmovcc, Endbr64, Syscall, Int3
    )
}
