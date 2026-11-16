//! UNION-MARKER-DEREF-READ-1 (2026-10-16, the review of the INTERIOR-MUT-CHANNEL-2
//! follow-ups): a read through a RECURSIVE union behind a reference, after a store to a
//! sibling field. The extractor spells a recursive type as a by-name marker
//! (`Ty::Datatype { name, variants: [] }`) wherever it occurs inside another type and
//! defines it once in the body's `datatype_defs`, so `RH.u` below is the marker `RU`, not
//! the stamped union. `local_defs::deref_read_unwritten_at`'s union refusal must see
//! through it: `h.u.next = None` writes the bytes `h.u.n` reads.
//!
//! `must_refute_*` are WRONG: each panics natively, at `-O0` and `-O3`, at the line
//! marked `// PANIC` on the input in its comment. `control_*` are CORRECT for every
//! input: the same shapes over a recursive STRUCT, whose fields lie side by side.
//! `tests/union_marker_deref_read_realmir.rs` pins the rows of the compiler's own
//! extraction of each (`tests/fixtures/union_marker_deref_read/`).
#![allow(dead_code, unused_unsafe, clippy::all)]

/// Recursive: a canonical cut point, spelled as a by-name marker inside other types.
/// `next = None` is the null pointer, so it writes 0 over `n`.
#[repr(C)]
pub union RU {
    pub n: usize,
    pub next: Option<&'static RU>,
}
pub struct RH {
    pub k: usize,
    pub u: RU,
}
pub struct RW<'a> {
    pub h: &'a mut RH,
}
/// The same fields in a recursive STRUCT: `next` lies beside `n`.
pub struct RS {
    pub n: usize,
    pub next: Option<&'static RS>,
}
pub struct RSH {
    pub k: usize,
    pub s: RS,
}
pub struct RSW<'a> {
    pub h: &'a mut RSH,
}

// h = &mut RH { k: 0, u: RU { n: 5 } }: `h.u.next = None` clears `h.u.n`, so at i = 0
// the read is 0 and `0 - 0 - 1` overflows (it panics for every n >= 1).
pub fn must_refute_recursive_union_in_struct(h: &mut RH) -> usize {
    let mut t = 0;
    for i in 0..unsafe { h.u.n } {
        h.u.next = None;
        t ^= unsafe { h.u.n } - i - 1; // PANIC
    }
    t
}

// w = &mut RW { h: &mut RH { k: 0, u: RU { n: 5 } } }: the same through a loaded `&mut RH`.
pub fn must_refute_recursive_union_via_loaded_ref(w: &mut RW) -> usize {
    let mut t = 0;
    for i in 0..unsafe { w.h.u.n } {
        w.h.u.next = None;
        t ^= unsafe { w.h.u.n } - i - 1; // PANIC
    }
    t
}

// Correct: the recursive struct, whose `next` store cannot reach `n`.
pub fn control_recursive_struct_in_struct(h: &mut RSH) -> usize {
    let mut t = 0;
    for i in 0..h.s.n {
        h.s.next = None;
        t ^= h.s.n - i - 1; // SAFE
    }
    t
}

// Correct: the recursive struct through a loaded `&mut RSH`.
pub fn control_recursive_struct_via_loaded_ref(w: &mut RSW) -> usize {
    let mut t = 0;
    for i in 0..w.h.s.n {
        w.h.s.next = None;
        t ^= w.h.s.n - i - 1; // SAFE
    }
    t
}
