//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: this function has no obligation of its own
//! MUTANT of `dyn_dispatch_reliance_cflow_concrete_sink.rs`: the enumerated case-split
//! member PANICS, so the `dyn` site must keep its obligation and the crate must
//! not verify.
//!
//! This is the guard that makes the C-FLOW rule a proof rather than a promise.
//! The provenance analysis reaches exactly the same conclusion as in the passing
//! fixture — the reachable target set is `{Sink}` — and then the case split asks
//! `<Sink as fmt::Write>::write_str` for an independent panic-freedom verdict and
//! is REFUSED, because the body contains `todo!()`.
//!
//! Two independent refusals are required and both are load-bearing:
//!
//! * the IMPL's own body fails — the diagnostic points at the panicking code,
//!   which is where its author can fix it; and
//! * `render` keeps its absent-callee obligation, i.e. the discharge did not
//!   happen. A rule that reported only the first would have laundered the panic
//!   into `render`'s verdict.
//!
//! HISTORY (2026-08): the first error briefly disappeared — a `todo!()` body
//! reported "1 proved, 0 failed" and this annotation was blessed into a NOTE
//! pinning that as a re-key strengthening. It was not: the body's only public
//! row is the whole-function panic-freedom aggregate, its per-site panic
//! obligation never becomes a counted row, and the structural subsumption
//! minted the aggregate Proved over a VACUOUS premise set (the todo!()
//! false-proof class; same family 4f7ad78ebd reverted two bundling gates
//! over). Premise (0) in `apply_whole_function_panic_freedom_subsumption` now
//! refuses that upgrade, and this ERROR is the pin that keeps it refused.
//!
//! POLICY (2026-10-27): the impl's assertion has a solver counterexample held
//! below proof authority. It remains UNKNOWN, not a certified refutation, but
//! `RowRefutationHeld` denies runtime-check tolerance: the panicking impl emits
//! Level 0 and strict errors. `render` independently keeps its consuming-site
//! error. Neither a held counterexample nor a proved neighboring row may make
//! the panicking body, or the caller relying on it, verify.
#![no_std]
#![allow(dead_code)]

use core::fmt;

pub struct Sink;

impl fmt::Write for Sink {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        //~^ ERROR Trust Level 0 safety verification incomplete
        //~| ERROR Trust strict verification failed
        todo!()
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
    //~^^^ ERROR Trust strict verification failed
}

// ZERO-ROW-GATE (2026-10-10): this rail must refuse for its OWN reason; a refusal by the
// zero-row gate (whose note is forbidden here) would mean the gate under test regressed
// into discharging and the zero-row gate masked it.
