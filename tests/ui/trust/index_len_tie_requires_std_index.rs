//@ revisions: default strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-fail
//@ dont-check-compiler-stderr
//! The nested-index LENGTH tie reads std's `Index<usize>` result on a std
//! container, never a method merely NAMED `index` (IDX-TIE-1, second consumer).
//!
//! `value_facts::build_immutable_index_len_tie_facts` ties `coll_len(a) ==
//! coll_len(b)` for two `index` calls at one stable index on one shared-ref root —
//! true for std's `Index<usize>` on a slice, array or `Vec` (the same element of an
//! unchanged container is the same inner collection). It recognized the callee by
//! `slice_conversion::is_slice_index_call`, the method tail `index`/`index_mut`, and
//! accepted any shared-ref root. Below, `LoV::index` returns a long `Vec` and
//! `HiV::index` an EMPTY one; the tie equated their lengths, so the `j <
//! LoV::index(t, i).len()` guard discharged `HiV::index(t, i)[j]` and the row read
//! `slice proved` (ay-in-process). The binary panics `index out of bounds: the len
//! is 0 but the index is 1` (std's own check still runs, so nothing is removed; the
//! row is a false proof that the default and strict policies accepted).
//!
//! BEFORE (stage 1 of integ/wave11 `936573497e`, `scratchpad/stage1-w11`; also
//! `stage1-w10`; each revision's flags with `--emit=metadata`, 2026-10-04): both
//! revisions built exit 0, `g`'s rows `slice proved` plus one `assert`
//! runtime-checked, and only the two warnings that row gives were emitted; the
//! `g` ERROR annotations below did not fire.
//!
//! AFTER (the fix): the tie requires `unwrap_panic::is_std_scalar_index_call` and a
//! root whose pointee is a slice, an array, the extractor's `Seq` (std's `Vec`) or
//! std's `Vec` by exact path. `g` gets no tie and its `slice` row is refuted. The
//! annotations were derived on the fixed stage 1 from a twin of this file in which
//! the user methods are renamed `idx` (which the old name test already refused);
//! that twin produced exactly the diagnostics annotated here.
//!
//! The control the builder was written for, std's nested `v[i][j]` on a shared
//! `&Vec<Vec<u32>>`, is `index_len_tie_std_nested_vec_still_proves.rs` (check-pass).

pub trait LoV {
    fn index(&self, i: usize) -> &Vec<u32>;
}
pub trait HiV {
    fn index(&self, i: usize) -> &Vec<u32>;
}

pub struct Two {
    pub long: Vec<u32>,
    pub empty: Vec<u32>,
}

impl LoV for Two {
    fn index(&self, _i: usize) -> &Vec<u32> {
        &self.long
    }
}
impl HiV for Two {
    fn index(&self, _i: usize) -> &Vec<u32> {
        &self.empty
    }
}

pub fn g(t: &Two, i: usize, j: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `index_len_tie_requires_std_index::g`: 2 obligation(s) were not proved
    //~| ERROR Trust strict verification failed for `index_len_tie_requires_std_index::g`
    if j < LoV::index(t, i).len() { HiV::index(t, i)[j] } else { 0 }
}
