// Counter-programs for a USER type whose path ends in `Vec`. Every recognizer that
// grants a fact about std's `Vec` (`generate::panic_calls::is_owned_slice_container_name`)
// tested the path's TAIL until 2026-09-30, so `user_type_named_vec::Vec` qualified.
// Its `Index` impl is its own: this one returns a different element on each call (a
// `Cell` flip; safe code, no `unsafe` anywhere). `value_facts`' `Vec` index/value tie
// (`build_vec_index_dest_value_tie_facts`) then equated the two `v[0]` reads, and the
// `[slice]` row of `s[v[0]]` and its hardened `BoundsCheck` twin were kernel-certified
// PROVED on the compiler's vcgen entry (MIR dumped by stage 1 a7ea88986d, whose own
// report for these bodies counts 2 of 5 obligations proved). Each `user_*` body panics
// natively (`index out of bounds: the len is 4 but the index is 18446744073709551615`,
// -O0 and -O3, `-C overflow-checks=on`) for `data = [0, usize::MAX]`.
//
// `slice_read_twice` is the PRECISION control: a `&[usize]` root keeps its element
// tie (a direct place read, `build_element_read_congruence_facts`), so the same
// guard still bounds the second read. It does not panic.
//
// Fixtures: tests/fixtures/user_type_named_vec_<fn>_mir.json, dumped from this file by
// Trust `main` stage 1 a7ea88986d with
//   rustc --edition 2024 --crate-type lib -Ztrust-verify-profile=unix_hardened \
//         -Ztrust-policy=advisory -Zub-checks=no -Ztrust-dump=mir:<dir> \
//         crates/trust-vcgen/tests/data/user_type_named_vec.rs
// run from the repository root (so `span.file` is already repo-relative; nothing in
// the dumps was edited).
#![allow(dead_code)]
use core::cell::Cell;

pub struct Vec {
    pub data: [usize; 2],
    pub flip: Cell<bool>,
}

impl core::ops::Index<usize> for Vec {
    type Output = usize;
    #[inline(never)]
    fn index(&self, _i: usize) -> &usize {
        let f = self.flip.get();
        self.flip.set(!f);
        &self.data[f as usize]
    }
}

pub fn user_vec_twice(s: &[u8], v: &Vec) -> u8 {
    if v[0] < s.len() { s[v[0]] } else { 0 }
}

// The same with the first read bound to a local.
pub fn user_vec_local(s: &[u8], v: &Vec) -> u8 {
    let i = v[0];
    if i < s.len() { s[v[0]] } else { 0 }
}

pub mod inner {
    // A generic user type named `Vec` in a nested module.
    pub struct Vec<T> {
        pub data: [T; 2],
        pub flip: core::cell::Cell<bool>,
    }
    impl<T> core::ops::Index<usize> for Vec<T> {
        type Output = T;
        #[inline(never)]
        fn index(&self, _i: usize) -> &T {
            let f = self.flip.get();
            self.flip.set(!f);
            &self.data[f as usize]
        }
    }
}

pub fn user_generic_vec_twice(s: &[u8], v: &inner::Vec<usize>) -> u8 {
    if v[0] < s.len() { s[v[0]] } else { 0 }
}

// PRECISION CONTROL: a slice's element is the same element at both reads.
pub fn slice_read_twice(s: &[u8], v: &[usize]) -> u8 {
    if !v.is_empty() && v[0] < s.len() { s[v[0]] } else { 0 }
}
