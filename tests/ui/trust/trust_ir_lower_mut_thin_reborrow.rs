//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-MR — the `&mut` twin of the thin identity reborrow): `&mut *r == r`
//! for a `&mut` reference, so the reborrow IS the value and the `Borrow{Mut}` arm
//! returns it verbatim, emitting nothing.
//!
//! WHY THIS PIN EXISTS. The lane closes a measured ASYMMETRY, not a missing model:
//! the SHARED spelling of every shape below already lowered clean through wave-TR,
//! while the `&mut` spelling declined under `Borrow(&mut non-local place)` — because
//! the arm accepted only a pointer this lowering itself minted and registered mutable
//! (`is_mut_borrow_ptr`). A genuine `&mut` the body RECEIVED but never created had no
//! arm at all. Each `mr_*` below is paired with its `sh_*` control so a regression
//! that reopens the gap shows up as the pair disagreeing, not as one body flipping.
//!
//! The two `neg_*` cases must STAY declining and are the reason this is a pin rather
//! than a smoke test — they are what the sixth conjunct and the shape gate refuse.
//! `neg_raw` is a raw-pointer reborrow (no provenance model); `neg_field` is a field
//! of a deref-rooted place (an address lane, not an identity reborrow).

pub struct S {
    pub x: u32,
    pub y: f64,
}

// (i) an unregistered `&mut` scalar-pointee param — `&mut f64` is not in the
// wave-5/23/HM registration set, so the pre-wave arm had nothing to match.
pub fn mr_f64(x: &mut f64) -> &mut f64 {
    x
}
pub fn sh_f64(x: &f64) -> &f64 {
    x
}

// (ii) a `&mut` whose pointee is itself a reference.
pub fn mr_refref<'a, 'b, T>(x: &'a mut &'b T) -> &'a mut &'b T {
    x
}
pub fn sh_refref<'a, 'b, T>(x: &'a &'b T) -> &'a &'b T {
    x
}

// (iii) RC-7, a correctness fix independent of yield: a DIVERGED inner is not a
// coverage gap. `todo!()` seals the block in the `!`-call arm and returns `None`;
// the pre-wave `_` arm could not tell that from a decline and tagged it. The SHARED
// spelling was already clean for exactly this reason.
pub fn mr_todo<'a>(_x: &'a mut u32) -> &'a mut u32 {
    todo!()
}
pub fn sh_todo<'a>(_x: &'a u32) -> &'a u32 {
    todo!()
}

// NEGATIVE CONTROLS — these must keep failing closed.
pub fn neg_raw(p: *mut u32) -> u32 {
    unsafe { *(&mut *p) }
}
pub fn neg_field(a: &mut S) -> &mut f64 {
    &mut a.y
}

pub fn main() {}
