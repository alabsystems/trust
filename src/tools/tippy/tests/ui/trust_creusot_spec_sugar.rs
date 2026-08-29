//! The disclosure arm of the creusot reader: every attribute here is OUTSIDE
//! the machine-applicable subset, so each gets a per-attribute disclosure
//! naming the blocker and the fix options (v7/D3), and NO rewrite is offered.
//! The machine-applicable twins live in trust_creusot_spec_sugar_fixable.rs.
// No machine-applicable fix is offered in this file, so there is nothing for
// rustfix to verify.
//@no-rustfix
#![feature(register_tool)]
#![register_tool(creusot_contracts)]
#![warn(clippy::trust_creusot_spec_sugar)]
#![allow(dead_code)]

// `@` lifts to mathematical Int: the recorded false-proof vector under
// Trust's exact-wrapping machine semantics. Disclosed, never rewritten.
#[creusot_contracts::ensures(result@ == x@ + 1)]
//~^ trust_creusot_spec_sugar
fn succ_view(x: u64) -> u64 {
    x + 1
}

// Int-relaxed quantifier: DEFERRED per the R4 §2 doctrine (auto-application
// waits for the bounded-domain encoding) — never auto-applied.
#[creusot_contracts::ensures(forall<i: Int> 0 <= i && i < 10 ==> x >= x)]
//~^ trust_creusot_spec_sugar
fn quantified(x: u64) -> u64 {
    x
}

// `^` is the pearlite prophecy (final value) operator; the `&mut` two-state
// lane is trust-wp's RustHorn prophecy domain.
#[creusot_contracts::ensures((^p) == 0)]
//~^ trust_creusot_spec_sugar
fn zero_it(p: &mut u32) {
    *p = 0;
}

// MutablePostStateAmbiguity: pearlite reads the ENTRY value of `x`; with a
// `mut` binding an exit-state re-reading would silently change the
// proposition, so the clause is refused even though its shape is supported.
#[creusot_contracts::ensures(result >= x)]
//~^ trust_creusot_spec_sugar
fn mut_param(mut x: u64) -> u64 {
    x += 1;
    x
}

// `old()` collapses only for immutable by-value parameters.
#[creusot_contracts::ensures(result == old(x))]
//~^ trust_creusot_spec_sugar
fn old_mut(mut x: u64) -> u64 {
    x += 0;
    x
}

// The pearlite-migration width hazard: a non-machine integer suffix is never
// silently stripped.
#[creusot_contracts::requires(x > 1int)]
//~^ trust_creusot_spec_sugar
fn suffixed(x: u64) -> u64 {
    x
}

const LIMIT: u64 = 10;

// Only parameter reads, `result`, `old(..)`, literals and machine operators
// are mapped; a free identifier is refused, not guessed.
#[creusot_contracts::ensures(result <= LIMIT)]
//~^ trust_creusot_spec_sugar
fn capped(x: u64) -> u64 {
    if x > LIMIT { LIMIT } else { x }
}

#[creusot_contracts::requires(result > 0)]
//~^ trust_creusot_spec_sugar
fn result_in_pre(x: u64) -> u64 {
    x
}

// Non-clause pearlite markers disclose per attribute with their own route.
#[creusot_contracts::variant(n)]
//~^ trust_creusot_spec_sugar
fn countdown(n: u64) -> u64 {
    if n == 0 { 0 } else { countdown(n - 1) }
}

#[creusot_contracts::logic]
//~^ trust_creusot_spec_sugar
fn spec_only(x: u64) -> u64 {
    x
}

#[creusot_contracts::trusted]
//~^ trust_creusot_spec_sugar
fn asserted() {}

// A family spelling with an unrecognized terminal is not this lint's
// business (negative control, mirrors kani::requires_nothing).
#[creusot_contracts::requires_nothing]
fn unrelated() {}

fn main() {}
