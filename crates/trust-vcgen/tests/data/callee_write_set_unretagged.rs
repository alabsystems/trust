// Counter-programs for the CALLEE WRITE-SET refinement
// (`generate::callee_write_set::refine_call_havoc_delta`) over a receiver whose pointee
// stores a pointer this function never retagged.
//
// The refinement replaces a `&mut` argument's base-name havoc with the paths the
// callee's own MIR writes through it. That is sound only when nothing under the
// pointee is a second hop out of the receiver's tree. Since 2026-09-30 (fd6dcb08d5)
// both of its refusals ask `path_defs::ty_reaches_unretagged_pointer`, which also
// sees a `&mut`, `Box` or raw pointer stored behind a `&` in the pointee; before, they
// asked `ty_contains_mut_pointer`, which does not recurse through `&`. Nothing pinned
// the change: with the old question put back, every test of the crate passed (the
// r8c finish's mutation ledger, mutant `MCWS_callee_write_set_old_check`). These
// bodies are the pin.
//
// `stored_mut_behind_shared` reads `**x.r` (a `&mut usize` stored behind a `&` in
// `*x`), calls a callee whose body writes nothing through `x` and whose one call takes
// no argument, and indexes with `**x.r` again. The callee's nested call writes the
// target through a raw copy stashed before the call: defined under Stacked Borrows and
// Tree Borrows alike, because the stored `&mut` is never retagged by this function
// (a read through it does not invalidate its raw children) and `x`'s protection covers
// the bytes of `*x`, not what a pointer stored in them points to. It panics natively
// (`index out of bounds: the len is 4 but the index is 18446744073709551615`, -O0 and
// -O3, `-C overflow-checks=on`).
//
// `stored_raw_behind_shared` and `stored_box_behind_shared` are the same shape with a
// raw pointer and a `Box` stored behind the `&`; each also panics natively.
//
// `frozen_field_across_a_callee_body` is the PRECISION control and the proof that the
// refinement is live in the harness: `x.n < s.len()` still bounds `s[x.n]` across a
// callee that writes nothing through `x` (no pointer is stored under `*x`'s `&`), but
// only when the callee's extracted body is in the summary database. Without it the
// base-name havoc of `x` kills the guard.
//
// Fixtures: tests/fixtures/callee_write_set_unretagged_<fn>_mir.json, dumped from this
// file by Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Zub-checks=no -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/callee_write_set_unretagged.rs
// run from the repository root (so `span.file` is already repo-relative; nothing in
// the dumps was edited). The callee bodies are fixtures too: the summary database the
// compiler builds carries each local non-generic callee's extracted body, keyed by the
// name its `Terminator::Call` carries.
#![allow(static_mut_refs, dead_code, unused_unsafe)]

/// A copy of the pointer the caller's caller stashed before the call.
pub static mut G: *mut usize = core::ptr::null_mut();

/// Takes no argument; writes through the stashed copy.
#[inline(never)]
pub fn poke_global() {
    unsafe {
        *G = usize::MAX;
    }
}

/// A `&mut usize` stored behind a shared reference.
pub struct MR<'a, 'b> {
    pub n: usize,
    pub r: &'a &'b mut usize,
}

/// Writes nothing through `x`; its one call takes no argument.
#[inline(never)]
pub fn touch_mr(_x: &mut MR) {
    poke_global();
}

pub fn stored_mut_behind_shared(s: &[u8], x: &mut MR) -> u8 {
    if **x.r < s.len() {
        touch_mr(x);
        s[**x.r]
    } else {
        0
    }
}

/// A raw pointer stored behind a shared reference.
pub struct PR<'a> {
    pub n: usize,
    pub p: &'a *mut usize,
}

#[inline(never)]
pub fn touch_pr(_x: &mut PR) {
    poke_global();
}

pub fn stored_raw_behind_shared(s: &[u8], x: &mut PR) -> u8 {
    if unsafe { **x.p } < s.len() {
        touch_pr(x);
        s[unsafe { **x.p }]
    } else {
        0
    }
}

/// A `Box` stored behind a shared reference.
pub struct BR<'a> {
    pub n: usize,
    pub b: &'a Box<usize>,
}

#[inline(never)]
pub fn touch_br(_x: &mut BR) {
    poke_global();
}

pub fn stored_box_behind_shared(s: &[u8], x: &mut BR) -> u8 {
    if **x.b < s.len() {
        touch_br(x);
        s[**x.b]
    } else {
        0
    }
}

/// Only a frozen target behind the `&`: nothing under `*x` is a second hop.
pub struct SR<'a> {
    pub n: usize,
    pub k: &'a usize,
}

#[inline(never)]
pub fn touch_sr(_x: &mut SR) {
    poke_global();
}

pub fn frozen_field_across_a_callee_body(s: &[u8], x: &mut SR) -> u8 {
    if x.n < s.len() {
        touch_sr(x);
        s[x.n]
    } else {
        0
    }
}
