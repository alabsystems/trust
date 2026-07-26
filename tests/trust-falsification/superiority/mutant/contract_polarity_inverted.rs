#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// TRAP (contract-completeness inc-1, POLARITY): the audit found a prior shape
// (`vc_to_trust_wp_contracts`) that INVERTED polarity — asserting the
// violation-formula AS the ensures — which false-Proves a wrong contract. This
// fixture is that hazard's witness: the postcondition `*r < x` is FALSE for the
// body `x + 1` (the result is GREATER than x, never less). A polarity-inverted
// prover (asserting `_0 < x` and finding a model, or proving `Not(_0 >= x)`)
// would spuriously discharge it. The CORRECT inc-1 ay path asserts the negated
// postcondition: the self-contained VC is
// `And([_0 == x + 1, x < 100, Not(_0 < x)])` = `_0 == x+1 AND x < 100 AND _0 >= x`,
// which is SATisfiable (e.g. x = 0, _0 = 1), so ay returns SAT and NO `Proved` is
// minted. The postcondition stays unproved — the polarity is right, the false
// contract is not proved.
#[core::contracts::requires(x < 100)]
#[core::contracts::ensures(move |r: &u32| *r < x)]
pub fn adds_one(x: u32) -> u32 {
    x + 1
}
