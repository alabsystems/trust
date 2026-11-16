//@ slice-facts: verifies
//! FLIPPED 2026-09-24 by D2 tier 1 (`ADAPTER_YIELD`, docs/TCB.md): the compiler
//! now installs the modeled fact that `Iterator::all` over `windows(2)` hands
//! this closure only length-2 sub-slices, and both rows prove (the closure's
//! report names the fact). The record below is what it was before — the
//! refusal this row existed to witness.
//!
//! `windows(2)` yields slices of length exactly 2, and the closure's root
//! verification does not know it. The counterexamples say so directly:
//! `w__slice_len = 1` and `w__slice_len = 0`. A FALSE REFUTATION of correct code.
//!
//! AND ITS WITNESS IS GROUNDABLE, which is now the cleanest way to tell this
//! half of the class from the other. Since `e00428dcb5` ("a true refutation was
//! delivered with a counterexample that contradicts the program") the LOOP rows
//! in this directory report `UNGROUNDED = no replayable witness could be
//! delivered` — their models were contradictory and the compiler now declines to
//! publish them. This row still delivers a concrete witness, because the length
//! here really IS unconstrained: the fact never reached the closure root, so a
//! length-0 slice is a genuine model. Missing fact here; unfoundable refutation
//! there.
pub fn f(v: &[u32]) -> bool { v.windows(2).all(|w| w[0] <= w[1]) }
