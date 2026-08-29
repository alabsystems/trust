//! The MODEL side of the differential: what `Aarch64Semantics` says a word does.
//!
//! This is deliberately built out of the SHIPPING pieces — `decode_aarch64`,
//! `Aarch64Semantics::effects`, `ConcreteState::apply_effect_with_eval_state` —
//! and adds nothing of its own. A differential whose model side is a
//! reimplementation tests the reimplementation.

use trust_disasm::decode_aarch64;
use trust_machine_sem::{
    Aarch64Semantics, ConcreteError, ConcreteFlags, ConcreteState, Effect, MachineState, Semantics,
};

use crate::ctx::{Profile, pattern_u64, scratch_range};
use crate::mutate::Mutation;

/// Why a word could not be compared. Never a verdict about the word — only
/// about this harness's ability to speak about it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Skip {
    /// The decoder refuses the word: it is not in the gate's antecedent at all.
    NotDecoded,
    /// The model refuses the word: `effects` failed, so no Proven can rest on it.
    NoEffects,
    /// The effect list is outside the concrete replayer's subset (control-flow
    /// effects, FP register writes, exclusive atomics). Not a model error —
    /// this harness simply cannot execute those effects concretely.
    UnsupportedEffect(String),
    /// A formula in the effect list could not be evaluated concretely.
    EvalError(String),
}

/// The model's predicted post-state for one word from one starting profile.
pub struct Predicted {
    pub gpr: [u64; 31],
    pub sp: u64,
    pub pc: u64,
    pub nzcv: u8,
    /// The predicted SIMD/FP file.
    pub fpr: [u128; 32],
    /// Predicted memory writes, as (8-byte-aligned address, whole 8-byte value).
    /// Only entries that DIFFER from the pattern appear.
    pub mem: Vec<(u64, u64)>,
    /// True when a predicted write fell outside the scratch window, so the
    /// hardware side cannot confirm or deny it.
    pub mem_outside_window: bool,
    /// True when the effect list READ memory outside scratch.
    ///
    /// The model will happily answer such a read from `pattern()`, because this
    /// harness seeds it on demand — but scratch is the only region whose
    /// contents the two sides share. A PC-relative literal load (`ldrsw x0,
    /// <label>`) reads the CODE arena, where the hardware sees `brk #1` filler
    /// and the model sees a pattern word that was never there. Comparing those
    /// would manufacture a disagreement out of the harness's own memory image,
    /// so such words are reported UNCHECKED instead.
    pub mem_read_outside_window: bool,
    /// True when the effect list WRITES x18. See the comparison in `main.rs`:
    /// x18 is the Darwin platform register and the OS resets it on some
    /// exception paths, so this harness cannot hold it, and a word that writes
    /// it is a measured blind spot rather than a quiet agreement.
    pub writes_x18: bool,
    /// True when the effect list READS x18 into some value it computes.
    ///
    /// THIS DIRECTION WAS MISSING, and it produced a flaky mismatch:
    /// `ands x4,x18,#0x1fc000001fc0` (f21a1a44) reported `model x4=0xc80 native
    /// x4=0x0` on one sweep and agreed on the next, because whether the OS had
    /// already reset x18 in that worker process depends on what ran before it.
    /// Excluding only the WRITE direction let a register this harness does not
    /// control flow into registers it does — and an oracle whose answer depends
    /// on its own history reports that history as a model bug.
    ///
    /// Kept separate from `writes_x18` because the two are excludable under
    /// different conditions — see the comparison site in `main.rs`. A read is
    /// untrustworthy only if the OS actually clobbered x18 for THAT candidate,
    /// which the observed record can settle; a write is never comparable.
    pub reads_x18: bool,
}

fn flags_to_bits(f: ConcreteFlags) -> u8 {
    u8::from(f.n) << 3 | u8::from(f.z) << 2 | u8::from(f.c) << 1 | u8::from(f.v)
}

/// Seed `state.memory` with the 8-byte pattern word containing `address`.
fn fill_pattern_word(state: &mut ConcreteState, address: u64) {
    let aligned = address & !7u64;
    let value = pattern_u64(aligned);
    for i in 0..8u64 {
        state.memory.insert(aligned + i, ((value >> (i * 8)) & 0xff) as u8);
    }
}

/// Run the model for one word at `pc`, starting from `profile`.
///
/// `mutation` is `Mutation::None` for every sweep and every recorded number.
/// The other variants exist so the gate can prove this differential still
/// FAILS when the model is wrong — see `mutate.rs`. The mutation is applied to
/// the effect list AFTER `Aarch64Semantics::effects` has produced it, so the
/// shipping crate is never edited and no restore can be forgotten.
///
/// MEMORY IS LAZY AND ON DEMAND. `ConcreteState` refuses to read an
/// uninitialized byte, which is the correct default — but the native side has a
/// whole 256 KiB region filled from `pattern()`, and materialising that as a
/// `BTreeMap` per word would dominate the run. So a read of an uninitialized
/// byte is answered by seeding exactly the pattern word it names and retrying.
/// The seeded value is the SAME function the C side filled scratch with, so the
/// two sides are reading one memory image, not two agreeing guesses.
pub fn predict(
    word: u32,
    pc: u64,
    profile: &Profile,
    mutation: Mutation,
) -> Result<Predicted, Skip> {
    let insn = decode_aarch64(&word.to_le_bytes(), pc).map_err(|_| Skip::NotDecoded)?;
    let sym = MachineState::symbolic();
    let effects =
        mutation.apply(Aarch64Semantics.effects(&sym, &insn).map_err(|_| Skip::NoEffects)?);

    // CONTROL-FLOW MARKERS ARE ANNOTATIONS, AND REFUSING THEM COST FOUR OPCODES.
    //
    // `Effect::Branch`/`Call`/`Return` carry no architectural post-state of
    // their own. `sem_b`, `sem_br`, `sem_bl`, `sem_blr` and `sem_ret` each emit
    // one of them ALONGSIDE the `Effect::PcUpdate` that says where the pc goes,
    // and `sem_bl` emits the X30 write as its own `RegWrite`. So the replayer's
    // blanket refusal of the marker put `B`, `BL`, `BLR` and `BR` outside this
    // oracle entirely — accepted by the model, reachable by the output gate,
    // and compared by nothing.
    //
    // MEASURED, not argued: with the marker refused, changing `sem_bl`'s
    // return address from `pc+4` to `pc+8` — a wrong link register for every
    // call in every emitted object — passed the FULL standing gate, PASS, no
    // new family. That is the exact false-Proven shape this harness exists to
    // catch, walking through the middle of it.
    //
    // GUARDED, NOT BLANKET. The markers are dropped only when the SAME effect
    // list also carries a `PcUpdate`. A list that branches without saying where
    // still reaches the replayer and is still refused, so this cannot quietly
    // become the dropped-`PcUpdate` hole wearing a filter.
    let effects: Vec<Effect> = if effects.iter().any(|e| matches!(e, Effect::PcUpdate { .. })) {
        effects
            .into_iter()
            .filter(|e| {
                !matches!(e, Effect::Branch { .. } | Effect::Call { .. } | Effect::Return { .. })
            })
            .collect()
    } else {
        effects
    };

    let mut pre = ConcreteState::new();
    pre.gpr = profile.gpr;
    pre.sp = profile.sp;
    pre.pc = pc;
    pre.flags = profile.flags();
    // The V file is part of the starting state on BOTH sides, or the comparison
    // over it would be a comparison of two different machines.
    pre.fpr = profile.fpr;

    let mut post;
    let mut rounds = 0usize;
    let mut mem_read_outside_window = false;
    loop {
        post = pre.clone();
        // THE GATE'S CONVENTION, adopted deliberately rather than invented here.
        // `Aarch64Semantics` omits `PcUpdate` entirely for some instructions
        // (`Opcode::Nop | Yield | Sev | Sevl | Prfm` return an EMPTY effect
        // list), and `verify_output.rs` reads an absent — or plainly sequential
        // — pc write as `pc += 4` at the bottom of its loop. So "no PcUpdate"
        // MEANS "falls through", and this replay must say the same thing or it
        // would report the model's convention as a hardware disagreement.
        //
        // The check keeps its teeth: the interesting failure is the model
        // claiming a fallthrough where the hardware BRANCHED, and that is
        // exactly what this still catches — it is the shape of the dropped
        // `Effect::PcUpdate` hole.
        post.pc = pc.wrapping_add(4);
        let mut failure = None;
        for effect in &effects {
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
                // A single instruction touches a bounded number of bytes; a run
                // away from that bound means the retry is not converging, and
                // guessing further would be inventing memory.
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

    // Predicted memory: every byte in `post.memory` that differs from the
    // pattern, promoted to whole 8-byte words so it can be compared against the
    // hardware diff (which is recorded at 8-byte granularity).
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
        let base = pattern_u64(aligned);
        let mut value = base;
        for i in 0..8u64 {
            if let Some(&b) = post.memory.get(&(aligned + i)) {
                value = (value & !(0xffu64 << (i * 8))) | (u64::from(b) << (i * 8));
            }
        }
        mem.push((aligned, value));
    }

    let writes_x18 = post.gpr[18] != pre.gpr[18]
        || effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 18, .. }));
    let reads_x18 = effects.iter().any(effect_mentions_x18);

    Ok(Predicted {
        gpr: post.gpr,
        sp: post.sp,
        pc: post.pc,
        nzcv: flags_to_bits(post.flags),
        fpr: post.fpr,
        mem,
        mem_outside_window,
        mem_read_outside_window,
        writes_x18,
        reads_x18,
    })
}

/// Does any formula this effect carries READ `X18`?
///
/// Asked of the free variables via `trust_types::collect_free_var_decls`, the
/// same collector the SMT discharge uses, rather than by matching effect shapes
/// — a shape match would have to enumerate every place a register can be read
/// (an address, a store value, a flag predicate, a branch condition) and would
/// silently miss the next one.
fn effect_mentions_x18(effect: &Effect) -> bool {
    let mentions = |f: &trust_types::Formula| {
        trust_types::collect_free_var_decls(f).iter().any(|(name, _)| name == "X18")
    };
    match effect {
        Effect::RegWrite { value, .. }
        | Effect::SpWrite { value }
        | Effect::FpRegWrite { value, .. }
        | Effect::PcUpdate { value } => mentions(value),
        Effect::MemWrite { address, value, .. } => mentions(address) || mentions(value),
        Effect::MemRead { address, .. } | Effect::Aarch64AtomicAccess { address, .. } => {
            mentions(address)
        }
        Effect::FlagUpdate { n, z, c, v } => {
            mentions(n) || mentions(z) || mentions(c) || mentions(v)
        }
        Effect::Branch { target } | Effect::Return { target } => mentions(target),
        Effect::ConditionalBranch { target, fallthrough, .. } => {
            mentions(target) || mentions(fallthrough)
        }
        Effect::Call { target, return_addr } => mentions(target) || mentions(return_addr),
        Effect::Aarch64SyncBoundary { .. } => false,
        // A variant added later carries formulas this function cannot see. Treat
        // it as TOUCHING x18 — excluding a word from comparison loses coverage
        // and says so in the count; comparing one whose value this harness does
        // not control manufactures a mismatch.
        _ => true,
    }
}
