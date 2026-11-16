//@ slice-facts: verifies
//! THE ROW THAT SPLIT THE CLASS IN TWO — AND THE HALF IT NAMED IS NOW CLOSED.
//! The filename keeps `and_it_still_refutes`: it was this row's own record, and
//! the sentence it is named for is the one the measurement retracted.
//!
//! WHAT IT RECORDED. Same program as c1 with the closure rewritten as a `for`
//! loop — no closure anywhere, so the "a closure is verified in isolation"
//! account could not explain it. Both counterexamples carried
//! `w__slice_len#s6_0 = 2`, the length postcondition IS in the model, and the
//! obligation refuted regardless. Two defects, not one.
//!
//! AND ITS DIAGNOSIS WAS RIGHT, which is why it is worth keeping. It said: "the
//! `#s6_0` suffix is the thread to pull … that is a version/encoding question,
//! NOT a missing fact, and it is not fixed by anything that carries call-site
//! facts into closures." Both halves held. The fix is a gate, not a fact, and it
//! moved no closure row.
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
pub fn f(v: &[u32]) -> bool {
    for w in v.windows(2) { if w[0] > w[1] { return false } }
    true
}
