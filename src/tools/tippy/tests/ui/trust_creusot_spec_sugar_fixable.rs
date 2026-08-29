//! The machine-applicable arm of the creusot reader (two-language design
//! v5, §3.2 MIGRATE): every attribute in this file is inside the supported
//! subset — boolean ops, comparisons, machine arithmetic, `old()` on
//! immutable by-value machine parameters, `result` — so rustfix must rewrite
//! the whole file to native signature clauses (see the .fixed twin, which is
//! also the pinned mapper output the blob-equivalence harness reads).
//! The spellings reach the lint as inert tool attributes (a real
//! creusot-contracts proc-macro dependency is consumed by expansion), so the
//! test registers the tool — the same technique as trust_legacy_spec_sugar.
#![feature(register_tool)]
#![register_tool(creusot_contracts)]
#![warn(clippy::trust_creusot_spec_sugar)]
#![allow(dead_code)]

#[creusot_contracts::ensures(result >= lo && old(lo) <= hi)]
//~^ trust_creusot_spec_sugar
fn floor_at(lo: u64, hi: u64) -> u64 {
    if lo > hi { hi } else { lo }
}

#[creusot_contracts::requires(x > 0 && x % 2 == 0)]
//~^ trust_creusot_spec_sugar
fn half(x: u32) -> u32 {
    x / 2
}

// requires + ensures on one carrier: ONE aggregated machine-applicable
// rewrite anchored at the first attribute, requires before ensures.
#[creusot_contracts::requires(lo <= hi)]
//~^ trust_creusot_spec_sugar
#[creusot_contracts::ensures(result <= hi)]
fn clamp_hi(x: u64, lo: u64, hi: u64) -> u64 {
    if x > hi {
        hi
    } else if x < lo {
        lo
    } else {
        x
    }
}

// Assoc fns in an impl are carriers too.
struct S;
impl S {
    #[creusot_contracts::ensures(result == n * n)]
    //~^ trust_creusot_spec_sugar
    fn square(n: u16) -> u16 {
        n * n
    }
}

// Twins of the blob-equivalence harness fixtures
// (targo-trust/tests/fixtures/creusot-equiv/): the harness binds its
// proposed side to THIS file's .fixed, so the mapper's rendering of these
// two rewrites is pinned here, in the mapper's own test lane.
#[creusot_contracts::ensures(x >= x)]
//~^ trust_creusot_spec_sugar
fn observe(x: u64) -> u64 {
    x
}

#[creusot_contracts::ensures(old(lo) <= lo)]
//~^ trust_creusot_spec_sugar
fn keep(lo: u64) -> u64 {
    lo
}

fn main() {}
