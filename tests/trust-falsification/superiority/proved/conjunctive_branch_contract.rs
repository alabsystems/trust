#![crate_type = "lib"]
#![feature(contracts)]
#![allow(incomplete_features)]
// SUPERIORITY: a CONJUNCTIVE postcondition `r >= lo && r <= hi` over a BRANCHING
// body (the `clamp` shape). rustc allows only one `#[ensures]` clause (combine with
// `&&`); Trust statically PROVES the whole conjunction across every branch — each
// conjunct is pinned to the branch's return value. Default mode must fully discharge
// it (this is the resolved "multiple-#[ensures]" case — conjunctive over branching).
#[core::contracts::requires(lo <= hi)]
#[core::contracts::ensures(move |r: &u32| *r >= lo && *r <= hi)]
pub fn clamp_contract(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}
