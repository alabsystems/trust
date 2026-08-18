//! NON-VACUITY — proving that this differential can still FAIL.
//!
//! An oracle that reports PASS is worth exactly as much as its ability to
//! report FAIL, and that ability decays silently. Every degradation this
//! harness has already suffered had the same shape: a register file that was
//! not loaded, an exclusion that swallowed a whole class, a comparison against
//! a field that was always zero on both sides. In each case the sweep still
//! printed a large `compared` count and `0 mismatches`, and the number meant
//! nothing. **A green run is evidence only if a wrong model would have been
//! red**, and that has to be demonstrated on the same run, not remembered from
//! the day the harness was written.
//!
//! So the gate injects the bug itself. Each `Mutation` below rewrites the
//! effect list that `Aarch64Semantics::effects` returned — AFTER the shipping
//! model produced it, never inside the shipping crate — into a model that is
//! wrong in one specific, named way. The differential is then run against the
//! mutant over the clang-assembled self-test corpus, and every mutation MUST be
//! caught. If any is not, the harness is reporting agreement it cannot see, and
//! the gate fails before a single sweep number is believed.
//!
//! EVERY MUTATION IS A BUG THAT ACTUALLY ESCAPED. This is not a list of
//! plausible errors; it is the fault log. `FpWriteToGpr` is family 1 of the
//! three divergences (a SIMD store modeled as a store of the GPR with the same
//! number). `SwapCarryOverflow` is the flag half of family 3 (`Adcs`/`Sbcs`
//! computing NZCV without the carry-in). `PerturbRegValue` is the shape of
//! family 2 (`Ubfm`/`Sbfm` producing a wrong VALUE from a correct register).
//! `DropPcUpdate` is the discarded `Effect::PcUpdate` hole. `DropFlagUpdate`,
//! `WrongDestReg` and `DropMemWrite` are the three mutations of the original
//! hand-run vacuity check, mechanised so they run every time instead of once.
//! `PerturbFpValue` and `PerturbPcTarget` guard two regions this oracle could
//! not see at all until the concrete replayer learned the FP round-trip shape
//! and the control-flow markers stopped being refused — and the second of them
//! has a measured escape behind it: `sem_bl` returning to `pc+8` instead of
//! `pc+4`, a wrong link register for every call in every emitted object,
//! passed the FULL standing gate.
//!
//! A BLANKET MUTATION IS A WEAKER GUARANTEE THAN IT LOOKS. Every entry here
//! rewrites a whole effect CLASS, so one word of the right kind catches it. All
//! three real divergences were NARROW and DATA-DEPENDENT — `imms < immr`, a
//! carry-in with `result == lhs`, an operand carrying `RegKind::Simd` — and a
//! narrow defect needs the triggering word to be IN the population before any
//! of this can see it. That the battery is green says the pipeline is live for
//! each state component; it does not say the population is rich enough. Both
//! properties were measured separately: a `carry_in AND result == lhs`
//! disjunct deleted from `compute_nzcv_with_carry` (family 3's boundary case
//! alone), an `LDP` with its two halves crossed, and `FSUB` computing an
//! addition were each written into the shipping source and each FAILED the
//! fast tier — Adcs=25/Sbcs=39, Ldp=300, Fsub=319.
//!
//! WHY POST-HOC REWRITING AND NOT AN EDIT TO THE MODEL. The original check was
//! performed by editing `aarch64/mod.rs`, running, and editing it back. That
//! demonstrated the same thing and could not be a gate: it is not repeatable
//! without a human, it cannot run in a clean tree, and a restore that was
//! forgotten would ship a deliberately broken model. Rewriting the returned
//! effect list keeps the shipping crate untouched — the mutation lives entirely
//! in the harness, which is the only place a deliberately wrong model belongs.
//!
//! A MUTANT MUST BE COMPARED, NOT REFUSED. A mutation that produced an
//! ill-sorted formula, or an effect the concrete replayer rejects, would push
//! its words into the UNCHECKED column and "catch" nothing — while looking, in
//! the exit code, exactly like a mutation that was caught. So every mutation
//! here is sort-preserving by construction, and the property is measured:
//! against the self-test corpus the shipping model compares 214 words and so
//! does every mutant, with an unchanged `effects outside the concrete replayer`
//! count. The single exception is `WrongDestReg` at 211, because shifting a
//! destination index onto `x18` moves three words into the platform-register
//! exclusion — an explained difference, not an unexplained one.
//!
//! WHAT THIS DOES NOT PROVE. Catching these nine mutations shows the pipeline
//! — decode, effects, concrete replay, native execution, comparison, reporting
//! — is live end-to-end for the state components each mutation disturbs
//! (`pc`, GPRs, the V file, NZCV, memory). It does NOT prove the differential
//! would catch an arbitrary eighth bug, and no finite battery could. It is a
//! floor, and the floor is what was missing.

use trust_machine_sem::Effect;
use trust_types::Formula;

/// A deliberate defect injected into the model side of the differential.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutation {
    /// The shipping model, unaltered. The only variant a sweep may run under.
    None,
    /// Drop every control-flow effect, so the model always claims fallthrough.
    DropPcUpdate,
    /// Rewrite a SIMD/FP register write into a write of the GPR with the same
    /// number.
    FpWriteToGpr,
    /// Drop every `FlagUpdate`, so NZCV never changes.
    DropFlagUpdate,
    /// Swap the carry-out and overflow formulas of every `FlagUpdate`.
    SwapCarryOverflow,
    /// Flip the low bit of every value written to a GPR.
    PerturbRegValue,
    /// Send every GPR write to the next register.
    WrongDestReg,
    /// Drop every store.
    DropMemWrite,
    /// Flip the low bit of every value written to a SIMD/FP register.
    PerturbFpValue,
    /// Move every branch target on by one instruction.
    PerturbPcTarget,
}

/// The battery the gate runs. Every one of these must be caught.
pub const BATTERY: [Mutation; 9] = [
    Mutation::DropPcUpdate,
    Mutation::FpWriteToGpr,
    Mutation::DropFlagUpdate,
    Mutation::SwapCarryOverflow,
    Mutation::PerturbRegValue,
    Mutation::WrongDestReg,
    Mutation::DropMemWrite,
    Mutation::PerturbFpValue,
    Mutation::PerturbPcTarget,
];

impl Mutation {
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Mutation::None => "none",
            Mutation::DropPcUpdate => "drop-pc-update",
            Mutation::FpWriteToGpr => "fp-write-to-gpr",
            Mutation::DropFlagUpdate => "drop-flag-update",
            Mutation::SwapCarryOverflow => "swap-carry-overflow",
            Mutation::PerturbRegValue => "perturb-reg-value",
            Mutation::WrongDestReg => "wrong-dest-reg",
            Mutation::DropMemWrite => "drop-mem-write",
            Mutation::PerturbFpValue => "perturb-fp-value",
            Mutation::PerturbPcTarget => "perturb-pc-target",
        }
    }

    pub fn from_name(s: &str) -> Option<Self> {
        std::iter::once(Mutation::None)
            .chain(BATTERY)
            .find(|m| m.name() == s)
    }

    /// The real fault this mutation reproduces, and the state component whose
    /// comparison must be alive for it to be caught. Printed by the gate, so a
    /// failure names the capability that was lost rather than only the mutation
    /// that slipped through.
    #[must_use]
    pub fn provenance(self) -> &'static str {
        match self {
            Mutation::None => "the shipping model",
            Mutation::DropPcUpdate => {
                "the discarded Effect::PcUpdate hole — proves the PC comparison is live"
            }
            Mutation::FpWriteToGpr => {
                "family 1: str d13 modeled as a store of X13 — proves the V file is loaded \
                 and compared"
            }
            Mutation::DropFlagUpdate => {
                "the ADDS-with-no-FlagUpdate mutation — proves NZCV is compared at all"
            }
            Mutation::SwapCarryOverflow => {
                "family 3: Adcs/Sbcs flags computed without the carry-in — proves NZCV is \
                 compared BIT BY BIT, not as a coarse changed/unchanged"
            }
            Mutation::PerturbRegValue => {
                "family 2: Ubfm/Sbfm right register, wrong value — proves GPR comparison is \
                 exact to one bit"
            }
            Mutation::WrongDestReg => {
                "the SUB-with-swapped-operands mutation — proves the WHOLE register file is \
                 compared, not the register the instruction was supposed to write"
            }
            Mutation::DropMemWrite => {
                "the store that does not happen — proves the memory diff is live, the one \
                 component the register file alone can never show"
            }
            Mutation::PerturbFpValue => {
                "a one-bit error in an FP RESULT — proves the SIMD/FP file is compared for \
                 the words whose value comes out of FP arithmetic, not only for the \
                 data-movement forms. Before the concrete replayer learned the \
                 `FpToIeeeBv(FpAdd(RNE, FpFromBits, FpFromBits))` shape, FADD/FSUB/FMUL/\
                 FDIV were refused outright: 3,000 words of each in the full-tier \
                 population, accepted by the model, reachable by the output gate, and \
                 compared by nothing."
            }
            Mutation::PerturbPcTarget => {
                "a branch that lands one instruction late — proves the newly-compared \
                 control-flow words are actually compared. `Effect::Branch`/`Call`/\
                 `Return` used to be refused by the replayer, which put B/BL/BLR/BR \
                 outside the oracle: changing `sem_bl`'s return address from pc+4 to \
                 pc+8 was MEASURED to pass the full standing gate."
            }
        }
    }

    /// Rewrite an effect list into the mutant's.
    ///
    /// Unknown effect variants pass through untouched: a mutation that silently
    /// dropped a variant it did not recognise would be a SECOND, unnamed defect
    /// riding along with the named one, and the count it produced would no
    /// longer be evidence about the thing it claims to test.
    #[must_use]
    pub fn apply(self, effects: Vec<Effect>) -> Vec<Effect> {
        match self {
            Mutation::None => effects,
            Mutation::DropPcUpdate => effects
                .into_iter()
                .filter(|e| {
                    !matches!(
                        e,
                        Effect::PcUpdate { .. }
                            | Effect::ConditionalBranch { .. }
                            | Effect::Branch { .. }
                    )
                })
                .collect(),
            Mutation::DropFlagUpdate => {
                effects.into_iter().filter(|e| !matches!(e, Effect::FlagUpdate { .. })).collect()
            }
            Mutation::DropMemWrite => {
                effects.into_iter().filter(|e| !matches!(e, Effect::MemWrite { .. })).collect()
            }
            Mutation::SwapCarryOverflow => effects
                .into_iter()
                .map(|e| match e {
                    // Both are Bool-sorted, so the swap is sort-preserving by
                    // construction: the mutant is a WRONG model, never an
                    // ill-typed one that would be rejected before it could be
                    // compared. A mutation the replayer refuses proves nothing.
                    Effect::FlagUpdate { n, z, c, v } => Effect::FlagUpdate { n, z, c: v, v: c },
                    other => other,
                })
                .collect(),
            Mutation::WrongDestReg => effects
                .into_iter()
                .map(|e| match e {
                    Effect::RegWrite { index, width, value } => {
                        Effect::RegWrite { index: (index + 1) % 31, width, value }
                    }
                    other => other,
                })
                .collect(),
            Mutation::PerturbRegValue => effects
                .into_iter()
                .map(|e| match e {
                    // `BvXor(v, 1, width)` at the SAME width the effect
                    // declares, so the replayer evaluates the operand exactly as
                    // it would have unmutated. A one-BIT error is deliberate: it
                    // is the most demanding thing to ask of the comparator, and
                    // family 2 was found by a comparison that had to be exact.
                    Effect::RegWrite { index, width, value } => Effect::RegWrite {
                        index,
                        width,
                        value: Formula::BvXor(
                            Box::new(value),
                            Box::new(Formula::BitVec { value: 1, width }),
                            width,
                        ),
                    },
                    other => other,
                })
                .collect(),
            Mutation::PerturbFpValue => effects
                .into_iter()
                .map(|e| match e {
                    // Same one-bit shape as `PerturbRegValue`, over the other
                    // register file, at the width the effect declares — so the
                    // mutant is compared rather than refused.
                    Effect::FpRegWrite { index, width, value } => Effect::FpRegWrite {
                        index,
                        width,
                        value: Formula::BvXor(
                            Box::new(value),
                            Box::new(Formula::BitVec { value: 1, width }),
                            width,
                        ),
                    },
                    other => other,
                })
                .collect(),
            Mutation::PerturbPcTarget => effects
                .into_iter()
                .map(|e| match e {
                    // ONE INSTRUCTION LATE, not dropped. `DropPcUpdate` proves
                    // the pc is compared at all; this proves the compared VALUE
                    // is the branch target and not merely "something changed".
                    Effect::PcUpdate { value } => Effect::PcUpdate {
                        value: Formula::BvAdd(
                            Box::new(value),
                            Box::new(Formula::BitVec { value: 4, width: 64 }),
                            64,
                        ),
                    },
                    other => other,
                })
                .collect(),
            Mutation::FpWriteToGpr => effects
                .into_iter()
                .map(|e| match e {
                    // EXACTLY family 1: the same register NUMBER, read out of
                    // the wrong file. 128-bit lanes are narrowed to 64 because
                    // a GPR write must be 32 or 64 bits wide — the historical
                    // bug had the same shape, since `read_gpr` only ever
                    // produced a 64-bit value.
                    Effect::FpRegWrite { index, width, value } => {
                        let (width, value) = if width > 64 {
                            (64, Formula::BvExtract { inner: Box::new(value), high: 63, low: 0 })
                        } else {
                            (width, value)
                        };
                        Effect::RegWrite { index: index.min(30), width, value }
                    }
                    other => other,
                })
                .collect(),
        }
    }
}
