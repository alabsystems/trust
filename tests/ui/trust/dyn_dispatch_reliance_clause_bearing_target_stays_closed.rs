//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! MUTANT: a case-split member that carries an AUTHORED CONTRACT CLAUSE must
//! refuse the discharge. A verdict computed under a clause is not an
//! unconditional panic-freedom verdict, and neither lane that reads
//! `dyn_dispatch_reliance::dyn_target_is_verified_panic_free` can discharge the
//! condition — a `dyn` site's receiver is erased, and the `write_fmt` reduction's
//! argument reaches its target through core frames that are not in the bundle.
//!
//! `S::tick` below is provably panic-free (`wrapping_add` cannot overflow-panic)
//! and its postcondition is proved, so EVERY other conjunct of the case split
//! passes: the coercion provenance is complete inside `drive`'s own bundle, the
//! target set is exactly `{S}`, and `<S as Tick>::tick` is a concrete local
//! `Item`. The ONLY thing that keeps `drive` red is the authored-clause conjunct.
//!
//! MEASURED on stage1 `c14d2e6ef` (the compiler WITHOUT that conjunct): this file
//! compiles CLEAN, and `TRUST_DYN_RELIANCE_PROBE=1` prints
//! `C-FLOW admitted 1 target(s)` / `site=<dyn …Tick>::tick => DISCHARGED`. So the
//! guard this file pins is one that has been watched to be missing.
//!
//! Three independent grounds make a clause-bearing target inadmissible, and the
//! rule needs only one:
//!
//! 1. A `requires` clause is CONJOINED INTO THE BODY'S OWN VCs as a hypothesis
//!    (`trust-mir-extract/src/lib.rs`: "contract preconditions become BODY
//!    hypotheses (`conjoin_live_preconditions`)"), so the verdict is conditional
//!    on a predicate the caller never has to establish here.
//! 2. A contract-bearing body can carry an INJECTED certified monitor that
//!    ABORTS when its clause fails (`certified_monitor_requires_entry.rs` is
//!    `run-crash` on "kernel-certified Trust monitor failed"). The body that runs
//!    is then not the body that was verified.
//! 3. This rule grounds the semantics of NO clause kind. What cannot be grounded
//!    fails closed — and a `matches!(kind, Requires | …)` list would silently
//!    readmit the next kind added to `TrustContractKind`.
//!
//! An `ensures` clause is used here deliberately: it is the ONLY authored clause
//! spelling this tree currently lets through to the case split with a clean
//! verdict (measured — a `requires`, `decreases`, or attribute clause each mints
//! its own unproved row and is declined for that reason instead). So it is the
//! one shape that isolates the conjunct. Widen the rule's exceptions and this
//! file goes green, which is a test failure.
#![no_std]
#![allow(dead_code)]

pub trait Tick {
    fn tick(&mut self, d: usize) -> usize;
}

pub struct S {
    n: usize,
}

impl Tick for S {
    // Panic-free on its own evidence; the clause is what makes it inadmissible.
    fn tick(&mut self, d: usize) -> usize
        ensures result == result
    {
        self.n = self.n.wrapping_add(d);
        self.n
    }
}

pub fn drive(s: &mut S) -> usize {
    let t: &mut dyn Tick = s;
    t.tick(0)
}
