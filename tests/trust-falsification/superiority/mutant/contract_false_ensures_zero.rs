#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// TRAP (contract-completeness inc-1): a FALSE postcondition. The body returns 1
// but the contract claims `*r == 0`. The ay contract-proving path added in inc-1
// must NOT statically discharge this: the self-contained VC is
// `And([_0 == 1, Not(_0 == 0)])` = `_0 == 1 AND _0 != 0`, which is SATisfiable
// (`_0 = 1`) — ay returns SAT, NOT a strict UNSAT proof, so no `Proved` is minted
// (the v1/ay bridge substitutes only a `Proved` for contract kinds, so the SAT
// leaves the obligation fail-closed). The postcondition therefore stays unproved
// (unknown/failed/runtime-checked), which is exactly what a mutant must do —
// proving the inc-1 ay contract proving is SOUND, not "prove everything".
#[core::contracts::ensures(move |r: &u32| *r == 0)]
pub fn returns_one() -> u32 {
    1
}
