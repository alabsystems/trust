// Counter-programs for a STANDARD-LIBRARY struct in the havoc of what a pointer this
// function never retagged can reach. Written for the r8c union's own walk
// (`unretagged_pointer_names_of`, 2026-09-30; replaced at landing, 2026-10-08, by
// CALL-HAVOC-ESCAPE-2's `generate::path_defs::stored_ref_pointee_names`, the one rule).
// A WIP carve-out of that walk (2026-09-30, never landed) treated every
// `alloc::`/`core::`/`std::` struct but `Box` as opaque, on the premise that a std
// struct's fields are private and so never spelled in a caller's body. The premise is
// false: `Range<*mut T>`'s `start` and `Wrapping<*mut T>`'s `.0` are public, and
// `*w.start` is a place in the caller's MIR. Under the carve-out the `[slice]` row of
// each of the first four bodies below, and its hardened twin, was kernel-certified
// PROVED on the compiler's entry: the r8c review's F2 and its pure-value twin,
// re-opened for a std struct. `stored_ref_pointee_names` skips std structs only in a
// body that never projects a std struct's field (`body_projects_into_std_adt`,
// fail-closed), and each body below projects one, so they are walked.
//
// Every `shared_*`/`mut_*`/`owned_*` body indexes after a callee set the pointee to
// `usize::MAX` and panics natively (`index out of bounds: the len is 4 but the index
// is 18446744073709551615`, -O0 and -O3, `-C overflow-checks=on`). The write is
// defined under Stacked Borrows and Tree Borrows alike: a raw pointer is not retagged,
// and a reference protects the bytes it covers, not what a pointer stored in them
// points to.
//
// The `vec_*` bodies write a `Vec`'s BUFFER through a copy of `as_mut_ptr()` taken
// before `&v`, between two `v[0]` reads. `as_mut_ptr` materializes no reference, and
// `&v` covers the `Vec`'s own bytes, not its buffer, so the write is defined and each
// body panics natively. They refute: the verifier's extraction renders `&Vec<T>` as
// `&Seq`, whose element reads are fresh call results with no tie between them
// (`value_facts::build_vec_index_dest_value_tie_facts` admits a `Vec` root only as an
// ADT rendered with its fields, which this extraction does not produce).
// `vec_len_guard_across_a_pure_value_call` is the PRECISION control: the length lives
// in the bytes `&v` freezes, and the guard still bounds `v[i]` across the call.
//
// Fixtures: tests/fixtures/std_struct_pointer_havoc_<fn>_mir.json, dumped from this
// file by Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Zub-checks=no -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/std_struct_pointer_havoc.rs
// run from the repository root (so `span.file` is already repo-relative; nothing in
// the dumps was edited). `-Zub-checks=no` keeps the pure-value skip on: with UB
// checks, the alignment check's cast is a laundering site that turns it off.
#![allow(static_mut_refs, dead_code, unused_unsafe)]

use core::ops::Range;
use std::num::Wrapping;

/// A copy of the pointer the caller's caller stashed before the call.
pub static mut G: *mut usize = core::ptr::null_mut();

/// Takes no argument; writes through the stashed copy.
#[inline(never)]
pub fn poke_global() {
    unsafe {
        *G = usize::MAX;
    }
}

#[inline(never)]
pub fn poke_usize(p: *mut usize) {
    unsafe {
        *p = usize::MAX;
    }
}

// The r8c review's F2 shape with `Range<*mut usize>` in place of a user struct: a
// callee handed a copy of the public field.
pub fn shared_range_raw_ptr(s: &[u8], w: &Range<*mut usize>) -> u8 {
    let i = unsafe { *w.start };
    if i < s.len() {
        poke_usize(w.start);
        s[unsafe { *w.start }]
    } else {
        0
    }
}

// The same, with a callee that takes no argument (the pure-value call skip).
pub fn shared_range_pure_value_call(s: &[u8], w: &Range<*mut usize>) -> u8 {
    let i = unsafe { *w.start };
    if i < s.len() {
        poke_global();
        s[unsafe { *w.start }]
    } else {
        0
    }
}

// A std tuple struct with a public raw-pointer field.
pub fn shared_wrapping_raw_ptr(s: &[u8], w: &Wrapping<*mut usize>) -> u8 {
    let i = unsafe { *w.0 };
    if i < s.len() {
        poke_usize(w.0);
        s[unsafe { *w.0 }]
    } else {
        0
    }
}

// A `&mut` parameter whose target holds the raw pointer: `&mut` protects the
// `Range`'s bytes, not what `start` points to.
pub fn mut_range_pure_value_call(s: &[u8], w: &mut Range<*mut usize>) -> u8 {
    let i = unsafe { *w.start };
    if i < s.len() {
        poke_global();
        s[unsafe { *w.start }]
    } else {
        0
    }
}

// An owned `Range<*mut usize>`. Refuted with and without the carve-out (a regression
// row, not evidence for the walk).
pub fn owned_range_pure_value_call(s: &[u8], w: Range<*mut usize>) -> u8 {
    let i = unsafe { *w.start };
    if i < s.len() {
        poke_global();
        s[unsafe { *w.start }]
    } else {
        0
    }
}

// A `Vec`'s buffer written through a copy of `as_mut_ptr()` stashed before `&v` was
// taken, between two `v[0]` reads.
pub fn vec_index_across_a_pure_value_call(s: &[u8], v: &Vec<usize>) -> u8 {
    if v[0] < s.len() {
        poke_global();
        s[v[0]]
    } else {
        0
    }
}

// The same, with the copy passed as an argument.
pub fn vec_index_across_a_pointer_call(s: &[u8], v: &Vec<usize>, p: *mut usize) -> u8 {
    if v[0] < s.len() {
        poke_usize(p);
        s[v[0]]
    } else {
        0
    }
}

// The same, with the first read bound to a local.
pub fn vec_index_local_across_a_pure_value_call(s: &[u8], v: &Vec<usize>) -> u8 {
    let i = v[0];
    if i < s.len() {
        poke_global();
        s[v[0]]
    } else {
        0
    }
}

// PRECISION CONTROL: the `Vec`'s length lives in the bytes `&v` freezes, so the guard
// bounds `v[i]` across a call that can write only the buffer. Does not panic.
pub fn vec_len_guard_across_a_pure_value_call(v: &Vec<u8>, i: usize) -> u8 {
    if i < v.len() {
        poke_global();
        v[i]
    } else {
        0
    }
}
