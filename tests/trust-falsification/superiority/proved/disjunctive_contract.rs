#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a DISJUNCTIVE postcondition `*r == x || *r == 0` over a BRANCHING
// body. Each branch returns one of the disjuncts, so the `||` holds on every path.
// Trust statically PROVES the disjunction (the `||` is lowered to a Formula::Or and
// each disjunct pinned per branch); rustc only checks it at runtime. Default mode
// must fully discharge it.
#[core::contracts::ensures(move |r: &u32| *r == x || *r == 0)]
pub fn disjunctive_contract(x: u32) -> u32 {
    if x > 0 {
        x
    } else {
        0
    }
}
