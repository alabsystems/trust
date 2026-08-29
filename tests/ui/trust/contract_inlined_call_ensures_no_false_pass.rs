//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! FALSIFICATION for the compositional spelling: naming a function in an
//! `ensures` must never make a FALSE clause pass.
//!
//! Deliberately on the SAME modeled `+` fragment as the positive twin, so the
//! refusal here is about the CLAUSE BEING FALSE and not about arithmetic the
//! verifier does not model — that separate direction is pinned by
//! `contract_inlined_call_unmodeled_arith_stays_closed`, and conflating the
//! two would let this fixture keep "failing" for a reason that proves nothing.
//!
//! `bump` adds one; the body adds two. The inline substitutes `bump`'s tail
//! expression over the actual, so the clause reads `result == (x) + (1)`
//! against a body returning `x + 2` — refutable, and it must be refuted. If
//! this fixture ever compiles, the inline is not denoting the callee's
//! expression: it either dropped the call to something vacuous or equated two
//! unrelated terms.
pub fn bump(v: u64) -> u64 requires v < 18446744073709551615 { v + 1 }

pub fn inc(x: u64) -> u64 requires x < 18446744073709551614 ensures result == bump(x) { x + 2 }
//~^ ERROR strict verification failed
