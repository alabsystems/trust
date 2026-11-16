//@ revisions: default strict
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ check-fail
//@ dont-check-compiler-stderr
//! A user trait method NAMED `len` is not the length of the `Vec` it borrows.
//!
//! `container_len::operand_is_len_of_place` read `_n = <..>::len(&w.v)` as
//! `len(w.v)` whenever the callee's method tail was `len`. The struct-field guard
//! lane (`build_len_guard_field_map`) then turned `if j < L::len(&w.v)` into the fact
//! `coll_len(w.v) > j` on the `w.v[j]` read, and the index's bounds row came back
//! `slice proved` (kernel-certified) although `L::len` here over-reports by 5:
//! `f(&W { v: vec![1, 2] }, 3)` panics with `index out of bounds: the len is 2 but
//! the index is 3`. Vec indexing is a call, so the check itself survives; the lie is
//! the proved row and the default policy's exit 0. The same value spelled honestly,
//! `Vec::len(&w.v).saturating_add(5)`, was already refused.
//!
//! BEFORE (stage 1 of `1ab78ed8e8`, `scratchpad/stage1-w10`; each revision's own
//! flags with `--emit=metadata`, diagnostics matched as compiletest matches them;
//! measured 2026-10-03): both revisions built exit 0. `f`, `f_ge` and `f_fq` each
//! carried only the two warnings `f_good` carries (their `assert` row is
//! runtime-checked), and the four ERROR annotations per revision below never fired.
//!
//! AFTER (predicted; it held on the stage 1 of `936573497e`, 2026-10-04): arm (a) of `operand_is_len_of_place` requires
//! `call_facts::is_std_inherent_len_call` — the std `Vec`/`String`/`VecDeque`/slice/
//! `str` length — so the user `len` mints no field-guard fact and the slice row of
//! `f`, `f_ge` and `f_fq` is not proved. The annotations were derived on the same
//! stage 1 from two twins of this file with only the user trait method renamed (to
//! `ln` and to `size_of_it`); both produced exactly the diagnostics annotated here.
//!
//! `f_good` is the control: genuine `w.v.len()` (extracted as
//! `alloc::vec::Vec::<u32>::len`) keeps the field-guard fact, its slice row stays
//! proved, and it keeps exactly the two warnings of its runtime-checked `assert` row.
//! compiletest requires every ERROR and WARN to be annotated, and this file does not
//! relax that, so a regression of the control fails the test.
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): on the merged stage 1 `f_good`'s
//! `assert` row is proved too (`1 proved`, kernel-certified: the soundness line's
//! bounds lane discharges the guarded `Vec` index), so the control now carries no
//! warning at all. `f`, `f_ge` and `f_fq` are refused exactly as annotated.

pub struct W {
    pub v: Vec<u32>,
}

pub trait L {
    fn len(&self) -> usize;
}

impl L for Vec<u32> {
    fn len(&self) -> usize {
        Vec::len(self).saturating_add(5)
    }
}

pub fn f(w: &W, j: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if j < L::len(&w.v) { w.v[j] } else { 0 }
}

pub fn f_ge(w: &W, j: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if L::len(&w.v) > j { w.v[j] } else { 0 }
}

pub fn f_fq(w: &W, j: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    if j < <Vec<u32> as L>::len(&w.v) { w.v[j] } else { 0 }
}

pub fn f_good(w: &W, j: usize) -> u32 {
    if j < w.v.len() { w.v[j] } else { 0 }
}
