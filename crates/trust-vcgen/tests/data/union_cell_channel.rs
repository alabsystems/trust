//! INTERIOR-MUT-CHANNEL-2 (2026-10-16, the review of G2-OPTSTRING-1): UnsafeCell bytes a
//! union's plain field names too. A shared borrow of a union's CELL field (or of a
//! field holding a `Vec` whose allocator holds a `Cell`) hands a callee a write channel
//! into bytes the union's other fields read, and a guard on such a field is stale after
//! the call. No hand edit: the cell bytes are read as a PLACE through the union sibling.
//!
//! `must_refute_*` are WRONG: each panics natively, at `-O0` and `-O3`, at the line
//! marked `// PANIC` on the input in its comment. `control_*` are CORRECT for every
//! input. `tests/union_cell_channel_realmir.rs` pins the rows of the compiler's own
//! extraction of each (`tests/fixtures/union_cell_channel/`).
#![feature(allocator_api)]
#![allow(dead_code, unused_unsafe, clippy::all)]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

/// An allocator holding a `Cell`: the bytes of a `Vec<u8, CA>` include cell bytes.
pub struct CA {
    pub c: Cell<usize>,
}
unsafe impl Allocator for CA {
    fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(l)
    }
    unsafe fn deallocate(&self, p: NonNull<u8>, l: Layout) {
        unsafe { Global.deallocate(p, l) }
    }
}
pub fn new_v(i: usize) -> Vec<u8, CA> {
    Vec::new_in(CA { c: Cell::new(i) })
}

pub union U32 {
    pub c: ManuallyDrop<Cell<u32>>,
    pub n: u32,
}
pub union UUS {
    pub c: ManuallyDrop<Cell<usize>>,
    pub n: usize,
}
pub struct WC {
    pub k: u8,
    pub u: UUS,
}
/// `n` overlays the `Vec`'s words; one of them is `CA.c` (word 2 on aarch64-apple-darwin).
pub union UV {
    pub v: ManuallyDrop<Vec<u8, CA>>,
    pub n: [usize; 4],
}
pub union UVO {
    pub v: ManuallyDrop<Option<Vec<u8, CA>>>,
    pub n: [usize; 4],
}

#[inline(never)]
pub fn poke_md_c32(c: &ManuallyDrop<Cell<u32>>) {
    c.set(u32::MAX)
}
#[inline(never)]
pub fn poke_md_c(c: &ManuallyDrop<Cell<usize>>) {
    c.set(usize::MAX)
}
#[inline(never)]
pub fn poke_vec(v: &Vec<u8, CA>) {
    v.allocator().c.set(usize::MAX)
}
#[inline(never)]
pub fn poke_md_v(v: &ManuallyDrop<Vec<u8, CA>>) {
    poke_vec(v)
}
#[inline(never)]
pub fn poke_md_vo(v: &ManuallyDrop<Option<Vec<u8, CA>>>) {
    if let Some(v) = &**v {
        poke_vec(v)
    }
}
#[inline(never)]
pub fn poke_uvo(x: &UVO) {
    unsafe { poke_md_vo(&x.v) }
}
#[inline(never)]
pub fn read_n(n: &usize) -> usize {
    *n
}

// v = 1: `u.n + 1` overflows.
pub fn must_refute_union_cell_field_add(v: u32) -> u32 {
    let u = U32 { n: v };
    if unsafe { u.n } < 100 {
        unsafe { poke_md_c32(&u.c) };
        unsafe { u.n + 1 } // PANIC
    } else {
        0
    }
}

// i = 1, s = [1, 2, 3].
pub fn must_refute_union_cell_field_index(i: usize, s: &[u8]) -> u8 {
    let u = UUS { n: i };
    if unsafe { u.n } < s.len() {
        unsafe { poke_md_c(&u.c) };
        s[unsafe { u.n }] // PANIC
    } else {
        0
    }
}

// i = 1, s = [1, 2, 3]: the union reached through a struct field (`&w.u.c`).
pub fn must_refute_struct_union_cell_field_index(i: usize, s: &[u8]) -> u8 {
    let w = WC { k: 1, u: UUS { n: i } };
    if unsafe { w.u.n } < s.len() {
        unsafe { poke_md_c(&w.u.c) };
        s[unsafe { w.u.n }] // PANIC
    } else {
        0
    }
}

// i = 1, s = [1, 2, 3], k = 2: only the allocator's cell bytes change.
pub fn must_refute_union_vec_field_index(i: usize, s: &[u8], k: usize) -> u8 {
    let u = UV { v: ManuallyDrop::new(new_v(i)) };
    if k < 4 && unsafe { u.n[k] } < s.len() {
        unsafe { poke_md_v(&u.v) };
        s[unsafe { u.n[k] }] // PANIC
    } else {
        0
    }
}

// i = 1, s = [1, 2, 3], k = 2: an `Option` over that `Vec` as the union field.
pub fn must_refute_union_option_vec_field_index(i: usize, s: &[u8], k: usize) -> u8 {
    let u = UVO { v: ManuallyDrop::new(Some(new_v(i))) };
    if k < 4 && unsafe { u.n[k] } < s.len() {
        unsafe { poke_md_vo(&u.v) };
        s[unsafe { u.n[k] }] // PANIC
    } else {
        0
    }
}

// i = 1, s = [1, 2, 3], k = 2: the whole union borrowed (G2-OPTSTRING-1's union rule).
pub fn must_refute_union_option_vec_whole_index(i: usize, s: &[u8], k: usize) -> u8 {
    let u = UVO { v: ManuallyDrop::new(Some(new_v(i))) };
    if k < 4 && unsafe { u.n[k] } < s.len() {
        poke_uvo(&u);
        s[unsafe { u.n[k] }] // PANIC
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_ovt(x: &Option<(Vec<u8>, UUS)>) {
    if let Some(t) = x {
        unsafe { poke_md_c(&t.1.c) }
    }
}
// x = Some((vec![1], UUS { n: 1 })), s = [1, 2, 3]: a `Vec` BESIDE a cell in an enum
// payload behind `&` (the enum is still named whole).
pub fn must_refute_option_vec_beside_union_cell(x: &Option<(Vec<u8>, UUS)>, s: &[u8]) -> u8 {
    unsafe {
        let a = match *x {
            Some((_, UUS { n })) => n,
            None => return 0,
        };
        if a < s.len() {
            poke_ovt(x);
            match *x {
                Some((_, UUS { n })) => s[n], // PANIC
                None => 0,
            }
        } else {
            0
        }
    }
}

// Correct: a borrow of the union's `Freeze` field hands out no write channel.
pub fn control_union_freeze_field_borrow_index(i: usize, s: &[u8]) -> u8 {
    let u = UUS { n: i };
    if unsafe { u.n } < s.len() {
        let _ = read_n(unsafe { &u.n });
        s[unsafe { u.n }] // SAFE
    } else {
        0
    }
}

#[inline(never)]
pub fn poke_uv(x: &UV) {
    unsafe { poke_md_v(&x.v) }
}
// x = &UV { v: ManuallyDrop::new(new_v(1)) }, s = [1, 2, 3], k = 2: the union behind `&`
// (the POINTEE half's walk passes through the union: G2-OPTSTRING-1's union rule).
pub fn must_refute_union_vec_behind_ref_index(x: &UV, s: &[u8], k: usize) -> u8 {
    if k < 4 && unsafe { x.n[k] } < s.len() {
        poke_uv(x);
        s[unsafe { x.n[k] }] // PANIC
    } else {
        0
    }
}

// ─── The discriminant read through a union sibling, behind `&` (no call) ────────
//
// `c[0]` overlays `e`'s tag word, and a raw store through a pointer cast from `&r.c`
// clears it between two `matches!(&r.e, Some(_))` reads. No call lies between them,
// so only `place_is_body_stable`'s union step keeps the discriminant CSE from tying the
// second read to the first (the review of the INTERIOR-MUT-CHANNEL-2 fix, b11 and b13).

/// `c[0]` overlays `e`'s tag word.
#[repr(C)]
pub union UT {
    pub e: Option<u32>,
    pub c: ManuallyDrop<[Cell<u32>; 2]>,
}
#[repr(C)]
pub struct HT {
    pub k: u32,
    pub u: UT,
}
/// The same two fields side by side (a struct): the cells do not overlay the tag.
#[repr(C)]
pub struct ST {
    pub e: Option<u32>,
    pub c: [Cell<u32>; 2],
}

// r = &UT { e: Some(7) }, s = [1, 2, 3]: the store clears the tag, so `b = 5`.
pub fn must_refute_union_tag_reread_after_raw_store(r: &UT, s: &[u8]) -> u8 {
    if s.len() < 3 {
        return 0;
    }
    if !matches!(unsafe { &r.e }, Some(_)) {
        return 0;
    }
    let p = unsafe { &r.c } as *const ManuallyDrop<[Cell<u32>; 2]> as *mut [u32; 2];
    unsafe { (*p)[0] = 0 };
    let b: usize = if matches!(unsafe { &r.e }, Some(_)) { 1 } else { 5 };
    s[b] // PANIC
}

// h = &HT { k: 0, u: UT { e: Some(7) } }, s = [1, 2, 3]: the union a struct field behind `&`.
pub fn must_refute_struct_union_tag_reread_after_raw_store(h: &HT, s: &[u8]) -> u8 {
    if s.len() < 3 {
        return 0;
    }
    if !matches!(unsafe { &h.u.e }, Some(_)) {
        return 0;
    }
    let p = unsafe { &h.u.c } as *const ManuallyDrop<[Cell<u32>; 2]> as *mut [u32; 2];
    unsafe { (*p)[0] = 0 };
    let b: usize = if matches!(unsafe { &h.u.e }, Some(_)) { 1 } else { 5 };
    s[b] // PANIC
}

// Correct: the struct twin, whose store hits the cells BESIDE the tag.
pub fn control_struct_tag_reread_after_raw_store(r: &ST, s: &[u8]) -> u8 {
    if s.len() < 3 {
        return 0;
    }
    if !matches!(&r.e, Some(_)) {
        return 0;
    }
    let p = &r.c as *const [Cell<u32>; 2] as *mut [u32; 2];
    unsafe { (*p)[0] = 0 };
    let b: usize = if matches!(&r.e, Some(_)) { 1 } else { 5 };
    s[b] // SAFE
}

// Correct: an owned union, the store into ANOTHER union.
pub fn control_other_union_tag_reread_after_raw_store(v: u32, s: &[u8]) -> u8 {
    let u = UT { e: Some(v) };
    let w = UT { e: Some(v) };
    if s.len() < 3 {
        return 0;
    }
    if !matches!(unsafe { &u.e }, Some(_)) {
        return 0;
    }
    let p = unsafe { &w.c } as *const ManuallyDrop<[Cell<u32>; 2]> as *mut [u32; 2];
    unsafe { (*p)[0] = 0 };
    let b: usize = if matches!(unsafe { &u.e }, Some(_)) { 1 } else { 5 };
    s[b] // SAFE
}
