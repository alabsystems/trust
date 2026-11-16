//@ slice-facts: verifies
//! THE LOOP DEFECT — CLOSED 2026-09-20. `windows(2)` yields length-2 sub-slices,
//! the fact was minted, and the row refuted anyway; that is what this file
//! recorded and it is no longer true of this program.
//!
//! THE WITNESS HISTORY IS WORTH KEEPING. Until 2026-09-19 this row published
//! `w__slice_len#s6_0 = 2` — index 0 is in bounds at length 2, so the
//! counterexample SATISFIED the constraint it was meant to violate. `e00428dcb5`
//! replaced it with `UNGROUNDED = no replayable witness could be delivered`,
//! which independently corroborated the spuriousness recorded here and was the
//! thread that led to the gate below.
//!
//! WHY "OBSERVABLE" IS IN THE NAME, and it still matters. An earlier version was
//!     for w in v.windows(2) { let _ = w[0]; }
//! and it VERIFIED — which I recorded as "one index proves, two refute", built a
//! minimal pair on, and committed. It was VACUOUS: the read is dead and is
//! eliminated, so nothing was checked. A passing row is a fact about the
//! instrument until the read it is supposed to check cannot be optimised away.
//!
//! WHAT CHANGED (2026-09-20). Not a fact, a GATE.
//! `v2_assert_len_binding_holds` ends by asking whether the indexed slice's fat
//! pointer is stable between the length read and the access, and it asked that
//! through `v2_slice_metadata_root_can_rebind` — "is this pointer rebound
//! ANYWHERE in the function". For a slice a loop yields the answer is always
//! yes: the loop rebinds it once per iteration. That write is in a DIFFERENT
//! execution of both endpoints and cannot decouple the pair this row is about,
//! so the binding was refused for every loop-carried slice there is, rustc's own
//! `BoundsCheck` assert was never recognised as covering the read, and the
//! rvalue-side twin of that assert was emitted and then refuted on a model the
//! program cannot produce.
//!
//! The question is now asked over the INTERVAL — the assert block's tail after
//! the length statement and the use block's prefix before the access, which is
//! all that can run given the sole-entry edge the caller already established.
//! The ALIAS half stayed whole-function on purpose: a `&mut s`/`&raw s`
//! anywhere is a channel through which a write can land inside the interval
//! invisibly, so it is not an interval question at all.
//!
//! WHAT IS NOT CLAIMED. This row is not PROVED. The redundant read row is gone;
//! rustc's `BoundsCheck` assert remains as the obligation, unproved and
//! runtime-checked, and the default policy REPORTS a gap whose obligations all
//! keep their runtime checks. The binary still bounds-checks. `v[0]` on an
//! unguarded slice is untouched and still fails with a verified counterexample
//! — the distinction that makes this a fix and not a laundering.
//!
//! WHAT STILL REFUSES, and it is the other half of the split this set found:
//! the CLOSURE forms (`c1`, `c3`, `g5`, `h1`, `h6`). There the `windows(n)`
//! postcondition never reaches the closure's own root at all, which no gate
//! change touches.
pub fn f(v: &[u32]) -> u32 { let mut s = 0u32; for w in v.windows(2) { s = s.wrapping_add(w[0]); } s }
