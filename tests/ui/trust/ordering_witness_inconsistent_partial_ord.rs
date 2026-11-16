//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ORD-WITNESS-CONSISTENT-1 (wave 16, 2026-10-05) — A COMPARISON GUARD READ AS
//! A FACT ABOUT AN ORDER THE TYPE NEVER PROMISED.
//!
//! EVERY ANNOTATED FUNCTION MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! # The defect
//!
//! The ordering-witness lane (`trust_vcgen::generate::witness_grounding`) grounds
//! a postcondition over a returned pair, `!matches!(r, Ok((d, c)) if d > c)`, on
//! the dominating comparison guard of the body: it reads `a <= b` on the `Ok`
//! edge as `d ≤ c` over the integers and discharges the contract's `d > c`
//! against it. The contract atom and the guard call two DIFFERENT operators, and
//! Rust does not enforce the `PartialOrd` laws: `Odd`'s `le` and `gt` both answer
//! `true`. Its sign sibling read a type's own `is_negative` / `is_positive` as
//! one trichotomy; `Sgn`'s both answer `true`. Both lanes keyed on the callee's
//! rendered name alone.
//!
//! BEFORE (stage 1 of `76a6ea45b2`, `scratchpad/stage1-w14`, each revision's own
//! flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-05):
//!
//! | function | `default` | `certify` |
//! |---|---|---|
//! | `pick_odd` | three `postcondition` rows `proved` (trust-exact-source-clause-discharge, ay-in-process ×2) | the same |
//! | `neg_only` | the same three rows `proved` | the same |
//!
//! Both revisions exit 0 with no diagnostic. The run-time witness is
//! `ordering_witness_inconsistent_partial_ord_run.rs`: `pick_odd(Odd(1), Odd(2))`
//! returns `Ok` with `d > c` true, so the proved `ensures` is false.
//!
//! # The fix
//!
//! The pair lane credits a guard only on a payload type the COMPILER found to be
//! one consistent total order (`trust_verify::order_consistent_adts`: builtin-
//! derived `PartialEq`/`PartialOrd`/any `Ord`, integer/`bool`/`char` fields or
//! such types, not generic), passed as `with_order_consistent_adts`. The sign
//! lane is retired.
//!
//! AFTER: not built when this file was written (FIX PREPARED 2026-10-05). The
//! annotations are what the BEFORE compiler prints for this file with each
//! guard replaced by a field comparison on the same line (`a.0 <= b.0`,
//! `c.0 < 0`): no witness call, so the payload terms stay ungrounded, as for
//! any unmodeled spec-model term (`SpecModelUngrounded`), and the function is
//! refused under both policies.
//!
//! The derived twin is `ordering_witness_derived_twin_never_reaches_the_lane.rs`.
#![feature(contracts)]
#![allow(incomplete_features)]
use core::cmp::Ordering;
use core::contracts::ensures;

// A hand-written `PartialOrd` whose operators disagree.
#[derive(Clone, Copy, PartialEq)]
pub struct Odd(pub u32);
impl PartialOrd for Odd {
    fn partial_cmp(&self, _o: &Odd) -> Option<Ordering> {
        None
    }
    fn le(&self, _o: &Odd) -> bool {
        true
    }
    fn gt(&self, _o: &Odd) -> bool {
        true
    }
}

#[ensures(|r: &Result<(Odd, Odd), u8>| !matches!(r, Ok((d, c)) if d > c))]
pub fn pick_odd(a: Odd, b: Odd) -> Result<(Odd, Odd), u8> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if !(a <= b) {
        return Err(1);
    }
    Ok((a, b))
}

// Inherent sign predicates that disagree.
#[derive(Clone, Copy, PartialEq)]
pub struct Sgn(pub i32);
impl Sgn {
    pub fn is_positive(&self) -> bool {
        true
    }
    pub fn is_negative(&self) -> bool {
        true
    }
}

#[ensures(|r: &Result<Sgn, u8>| !matches!(r, Ok(c) if c.is_positive()))]
pub fn neg_only(c: Sgn) -> Result<Sgn, u8> {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if !c.is_negative() {
        return Err(1);
    }
    Ok(c)
}
