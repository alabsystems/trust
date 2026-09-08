//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-FW: the FIELD of a DEREF-ROOTED place — `&(*p).f` / `&mut (*p).f` and the
// auto-deref spellings — lowers as a byte-offset GEP off the base pointer's
// VALUE, with the ledger class INHERITED from the base (ref-param bases join
// interior_ptrs and may tail-return; frame-derived bases join
// frame_interior_ptrs and the return-escape guards keep refusing them — the
// Addendum 3 laundering hazard this lane was scheduled behind).

pub struct S {
    pub a: i64,
    pub b: u32,
}

pub fn shared_autoderef(p: &S) -> &u32 {
    &p.b
}

pub fn shared_explicit(p: &S) -> &i64 {
    &(*p).a
}

pub fn mut_tail(p: &mut S) -> &mut u32 {
    // the tail spelling arrives wrapped `&mut *(&mut (*p).b)`; the helper's
    // kind-aware `*&place` unwrap is what admits it
    &mut p.b
}

pub fn mut_store(p: &mut S) {
    let r = &mut (*p).a;
    *r = 9;
}

// wave-FI-a: DEPTH-N field chains compose to ONE flat-I8 GEP at the SUM of
// the per-level rustc byte offsets (each level individually gated), and an
// INTERIOR-pointer base inherits the outliving class — its referent outlives
// the call by the ledger's own definition, and a field offset stays
// statically within the referent.
pub struct Outer {
    pub inner: S,
    pub tag: u32,
}

pub fn deep(o: &Outer) -> &i64 {
    let foo = &o.inner;
    &foo.a
}

pub fn deep2(o: &Outer) -> &u32 {
    &o.inner.b
}

// wave-FI-b: an OUTER index over the chain — the dynamic-index bounds idiom
// verbatim (Const len + ICmp Ult + Assert(InBounds) + the recorded
// BoundsCheck obligation), then a scaled displacement composed onto the
// summed field offset. With the assert, the address stays inside the array
// field, which stays inside the referent — the FI-a inheritance carries.
pub struct WithArr {
    pub tag: u32,
    pub xs: [i64; 3],
}

pub fn pick(w: &WithArr, i: usize) -> &i64 {
    let foo = &w.xs;
    let _ = foo;
    &w.xs[i]
}

// wave-FI-c: BOX levels mid-chain — segments split at box autoderefs; each
// split GEPs to the box field, Loads the data pointer (offset 0, wave-BX
// gated), and continues on the heap block with the structured inheritance
// (a Box owned by outliving memory is dropped by its owner, so the block
// outlives the call — the wave-FIL doc's own argument, never B0's
// unconditional-frame rule for arbitrary ptr lanes).
pub struct Boxed {
    pub k: u32,
    pub d: Box<S>,
}

pub fn through_box(b: &Boxed) -> &i64 {
    &b.d.a
}

fn main() {}
