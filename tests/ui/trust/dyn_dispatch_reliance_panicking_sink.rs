//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
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
//! Two distinct errors are required and both are load-bearing:
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
//! POLICY (2026-08-14): with the vacuous mint refused, the impl side surfaces
//! as a WARN, not an ERROR — the dyn-reliance case split verifies `write_str`
//! as a PREMISE body under an explicitly nonfatal policy (even `-Ztrust-policy
//! =strict` does not change it; measured), so the enforcement error fires ONCE
//! at the consuming site. Both load-bearing properties hold in the new
//! spelling: the WARN points at the panicking body (author's fix site) and
//! `render`'s ERROR proves the discharge did not happen. When refutation
//! authority returns (producer attestation), the impl side should REFUTE and
//! this WARN should be upgraded back to that ERROR.
#![no_std]
#![allow(dead_code)]

use core::fmt;

pub struct Sink;

impl fmt::Write for Sink {
    fn write_str(&mut self, _s: &str) -> fmt::Result {
        //~^ WARN Trust Level 0 safety verification incomplete
        todo!()
    }
}

pub fn render(sink: &mut Sink) -> fmt::Result {
    use fmt::Write as _;
    write!(sink, "constant")
    //~^^^ ERROR Trust strict verification failed
}
