//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// F1 Increment A (adversarially reviewed, docs/design/2026-08-31-f1-value-
// transport-entry.md review record): `&mut (*p).f` where `f` is a raw-pointer
// field mints its interior GEP — MUT PATH ONLY. The shared side stays refused
// (R3's re-route surface: the wave-25 off==0 verbatim-pv tautology serves it),
// every downstream consumer of the minted address still fails closed (the
// Store's scalar wall + !is_borrow_ptr fence; the Deref arm's Ptr-pointee
// refusal), and Increment B may not widen further without the review's
// converged loaded-ptr rule — R2's memory-transport false-verify channel.

pub struct S {
    pub p: *mut i64,
    pub n: u32,
}

pub fn take_mut(s: &mut S) {
    let t = &mut s.p;
    let _ = t;
}

fn main() {}
