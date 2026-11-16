#![crate_type = "lib"]
// Trust R3 prerequisite P0 (probe T5d): a GENERIC caller of a bodyless trait
// method. No body exists ANYWHERE for `D::m`, yet before the counted-carrier
// fix this compiled clean (rc=0) under the default strict policy — panic-freedom
// claimed for a callee that does not exist.
//
// SINCE OD-1 PHASE 1 (c77d7678cf, 2026-10-04; docs/DECISION_QUEUE.md OD-1) this
// call is an ADMITTED open generic dispatch: the body no longer claims
// panic-freedom for every instantiation, and the site mints an
// `assumption:instance-hypothesis` row instead of the absent-callee refutation.
// Measured on a stage 1 of main + wave 17 (2026-10-06):
//   * `-Ztrust-policy=certify` (this gate): exit 1, "Trust certify verification
//     failed … 1 instance hypothesis row(s) — … assumed, not proved" (memory-safe
//     also exits 1, with its own "Trust memory-safe verification failed").
//     That is an INCOMPLETENESS refusal, so the gate scores this row `incomplete`
//     and prints UNCAUGHT MUTANT: nothing is refuted, because without a concrete
//     instance there is no counterexample to exhibit.
//   * default and strict: exit 0 with a warning, the crate's result CONDITIONAL
//     ("ASSUMED per instance, not proved").
// The row stays in the mutant lane, red on purpose: removing it would shrink the
// mutation denominator to turn the gate green (FALSIF-OD1-VOCAB).
pub trait D {
    fn m(&self) -> u32;
}
pub fn r3_t_default<T: D>(t: &T) -> u32 {
    t.m()
}
