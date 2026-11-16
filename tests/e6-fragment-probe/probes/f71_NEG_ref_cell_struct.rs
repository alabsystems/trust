//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. A `Cell<u32>` SIBLING field beside the scalar
//@ probe-note: the contract reads.
//@ probe-note: WHICH NET REFUSES IT — UPDATED AT I2, 2026-09-19, and this is the whole
//@ probe-note: cost of that increment. `trust_frozen_shared_param_scan` decides C2
//@ probe-note: (`Ty::is_freeze`) first, and a struct with a `Cell` field is not `Freeze`.
//@ probe-note: Under I1 a SECOND net also caught it: `trust_e6_view_carrier` reads the
//@ probe-note: DECLARED field type and `Cell<u32>` is a `ty::Adt`, outside the scalar
//@ probe-note: vocabulary — it does NOT recurse into nested ADTs, so "`Cell<u32>` is
//@ probe-note: `u32` all the way down" is not a thing this lane ever computes — and the
//@ probe-note: flattening was ALL-OR-NOTHING (D-REF-8), so one such field refused the
//@ probe-note: pointee.
//@ probe-note: **THAT SECOND NET IS GONE.** I2 (disposition R4, implementer-proposed) skips a field outside the
//@ probe-note: vocabulary so its scalar siblings can carry a contract, and a `Cell` sibling
//@ probe-note: is skipped exactly like `f80`'s `Vec<u8>`. C2 and K2 are the ONLY thing
//@ probe-note: holding this line, and neither is kernel-checked
//@ probe-note: (`docs/TCB.md`, `EnsuresCitationViewDischarge`). The sibling rows in the
//@ probe-note: same state are `f91` (an `UnsafeCell` sibling) and `f84` (the whole
//@ probe-note: pointee), against the `Freeze` twin `f85`. THE MUTATION CONTROL WAS RUN,
//@ probe-note: 2026-09-19, both directions on a stage-1 build: with BOTH `is_freeze` and
//@ probe-note: `trust_k2_no_inline_unsafe_cell` stubbed out this probe goes `discharged`
//@ probe-note: (so do `f84` and `f91`, while `f85` is unchanged), and restoring both
//@ probe-note: guards returns it to `clause-outside-fragment`. A bless that turns this
//@ probe-note: row green is that regression, not churn.
clean { def id32c (x : UInt32) : UInt32 := x }
use std::cell::Cell;
pub struct Counter { pub n: u32, pub hits: Cell<u32> }
impl Counter {
    pub fn n_of(&self) -> u32
        ensures result == id32c(self.n)
    { self.n }
}
