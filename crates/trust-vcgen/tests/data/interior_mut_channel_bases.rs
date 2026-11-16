// The real-MIR bases of the hand-built interior-mutability bodies in
// `tests/interior_mut_channel_realmir.rs` (the verifier-gaps design, Appendix A.7
// and C). rustc keeps `Cell::new`/`get`/`set` as calls in the verify MIR even at
// `-C opt-level=3`, so the false proofs those bodies pin are reachable only where a
// cell's bytes are read as a place: the hand edit replaces each `Cell` call by the
// place read it performs (`c.0.0`), leaving every call that hands out `&c` in place.
// Each base is ALSO a correct program as written (`&usize`, no cell), and its row
// proves; the edited body is the native twin below, which panics.
#![allow(clippy::all, unused_mut, unused_assignments, dead_code)]
use std::cell::Cell;

// Base of `synthetic_shared_slice_of_cells` (`a: &[usize]` -> `&[Cell<usize>]`).
#[inline(never)]
pub fn poke(_c: &usize) {}
pub fn cell_slice_interior(a: &[usize], s: &[u8], i: usize, k: usize) -> u8 {
    let mut j = 0usize;
    if k > 1000 {
        j = i;
    }
    if j < a.len() && k < a.len() && a[j] < s.len() {
        poke(&a[k]);
        s[a[j]]
    } else {
        0
    }
}

// Bases of the two holder bodies (`W.r: &usize` -> `&Cell<usize>`).
pub struct W<'a> {
    pub r: &'a usize,
}
#[inline(never)]
pub fn poke_global() {}
pub fn pv_mut_holder(w: &mut W, s: &[u8]) -> u8 {
    if *w.r < s.len() {
        poke_global();
        s[*w.r]
    } else {
        0
    }
}
pub fn pv_shared_holder(w: &W, s: &[u8]) -> u8 {
    if *w.r < s.len() {
        poke_global();
        s[*w.r]
    } else {
        0
    }
}

// Base of `synthetic_cell_interior_callee` and its twins (dumped at -C opt-level=3).
#[inline(never)]
pub fn poke_cell(c: &Cell<usize>) {
    c.set(usize::MAX);
}
pub fn local_cell_callee(s: &[u8]) -> u8 {
    let c = Cell::new(0usize);
    if c.get() < s.len() {
        poke_cell(&c);
        s[c.get()]
    } else {
        0
    }
}

// Native twins of the edited bodies (real cells, `.get()` for the interior read);
// each panics at -O0 and -O3 on the input in its comment. Not dumped.
//
// a = [Cell::new(0), Cell::new(0)], s = [7; 4], i = 0, k = 0:
//     pub fn cell_slice_interior(a: &[Cell<usize>], s: &[u8], i: usize, k: usize) -> u8 {
//         let mut j = 0usize; if k > 1000 { j = i; }
//         if j < a.len() && k < a.len() && a[j].get() < s.len() { poke(&a[k]); s[a[j].get()] } else { 0 }
//     }
//     #[inline(never)] pub fn poke(c: &Cell<usize>) { c.set(usize::MAX); }
//
// A `Box::leak`ed `&'static Cell(0)` stored in `T` and in `w.r`, s = [1, 2, 3]; no `unsafe`:
//     thread_local! { static T: Cell<Option<&'static Cell<usize>>> = const { Cell::new(None) }; }
//     #[inline(never)] pub fn poke_global() { T.with(|t| if let Some(c) = t.get() { c.set(usize::MAX) }) }
//     pub struct WC<'a> { pub r: &'a Cell<usize> }
//     pub fn pv_mut_holder(w: &mut WC, s: &[u8]) -> u8 {
//         if w.r.get() < s.len() { poke_global(); s[w.r.get()] } else { 0 }
//     }
