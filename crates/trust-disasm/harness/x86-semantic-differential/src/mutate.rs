//! NON-VACUITY: deliberately wrong effect lists the differential must catch.
//!
//! Applied AFTER `X86_64Semantics::effects`, so the shipping crate is never
//! edited and no restore can be forgotten — the same design as the AArch64
//! twin's battery, for the same reason: a differential that has quietly
//! stopped comparing something reports agreement, and agreement from a blind
//! oracle is the failure the gate exists to prevent.

use trust_machine_sem::Effect;
use trust_types::Formula;

pub const BATTERY: &[&str] = &[
    "drop-flag-update",
    "drop-mem-write",
    "drop-pc-update",
    "perturb-reg-value",
    "wrong-dest-reg",
    "perturb-pc-target",
];

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mutation {
    None,
    DropFlagUpdate,
    DropMemWrite,
    DropPcUpdate,
    PerturbRegValue,
    WrongDestReg,
    PerturbPcTarget,
}

impl Mutation {
    pub fn parse(name: &str) -> Option<Self> {
        Some(match name {
            "drop-flag-update" => Self::DropFlagUpdate,
            "drop-mem-write" => Self::DropMemWrite,
            "drop-pc-update" => Self::DropPcUpdate,
            "perturb-reg-value" => Self::PerturbRegValue,
            "wrong-dest-reg" => Self::WrongDestReg,
            "perturb-pc-target" => Self::PerturbPcTarget,
            _ => return None,
        })
    }

    pub fn apply(self, effects: Vec<Effect>) -> Vec<Effect> {
        fn plus_one(f: Formula) -> Formula {
            Formula::BvAdd(Box::new(f), Box::new(Formula::BitVec { value: 1, width: 64 }), 64)
        }
        match self {
            Mutation::None => effects,
            Mutation::DropFlagUpdate => {
                effects.into_iter().filter(|e| !matches!(e, Effect::FlagUpdate { .. })).collect()
            }
            Mutation::DropMemWrite => {
                effects.into_iter().filter(|e| !matches!(e, Effect::MemWrite { .. })).collect()
            }
            Mutation::DropPcUpdate => {
                effects.into_iter().filter(|e| !matches!(e, Effect::PcUpdate { .. })).collect()
            }
            Mutation::PerturbRegValue => effects
                .into_iter()
                .map(|e| match e {
                    Effect::RegWrite { index, width, value } => {
                        Effect::RegWrite { index, width, value: plus_one(value) }
                    }
                    other => other,
                })
                .collect(),
            Mutation::WrongDestReg => effects
                .into_iter()
                .map(|e| match e {
                    Effect::RegWrite { index, width, value } => {
                        Effect::RegWrite { index: (index + 1) % 16, width, value }
                    }
                    other => other,
                })
                .collect(),
            Mutation::PerturbPcTarget => effects
                .into_iter()
                .map(|e| match e {
                    Effect::PcUpdate { value } => Effect::PcUpdate { value: plus_one(value) },
                    other => other,
                })
                .collect(),
        }
    }
}
