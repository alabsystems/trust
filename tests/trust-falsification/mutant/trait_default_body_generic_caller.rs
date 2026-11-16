#![crate_type = "lib"]
// Trust R3 soundness guard (probe T5b, blueprint §5): a generic caller of a
// trait method WITH a default body. Before the bundling guard,
// `Instance::try_resolve` returned Ok(None) for `<T as D>::m`, the collector
// fell back to the syntactic trait-method DefId, bundled the DEFAULT body,
// and the bridge lowered a real call INTO it — proving the caller's
// panic-freedom against a body an impl may OVERRIDE with a panicking one
// (a downstream `impl D for P { fn m(&self) -> u32 { panic!() } }` +
// `r3_t_default(&P)` panics at runtime). The default body may be trusted only
// when the instance RESOLVES to it.
//
// SINCE OD-1 PHASE 1 (c77d7678cf, 2026-10-04; docs/DECISION_QUEUE.md OD-1) the
// call is an ADMITTED open generic dispatch: it mints an
// `assumption:instance-hypothesis` row, and the default body is still never
// trusted for an unresolved instance. Measured on a stage 1 of main + wave 17
// (2026-10-06):
//   * `-Ztrust-policy=certify` (this gate): exit 1, "Trust certify verification
//     failed … 1 instance hypothesis row(s) — … assumed, not proved" (memory-safe
//     also exits 1, with its own "Trust memory-safe verification failed").
//     That is an INCOMPLETENESS refusal, so the gate scores this row `incomplete`
//     and prints UNCAUGHT MUTANT: no counterexample exists without a concrete
//     panicking instance in the crate.
//   * default and strict: exit 0 with a warning, the crate's result CONDITIONAL
//     ("ASSUMED per instance, not proved").
// The row stays in the mutant lane, red on purpose (FALSIF-OD1-VOCAB).
pub trait D {
    fn m(&self) -> u32 {
        1
    }
}
pub fn r3_t_default<T: D>(t: &T) -> u32 {
    t.m()
}
