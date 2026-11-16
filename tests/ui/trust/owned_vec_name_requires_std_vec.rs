//@ revisions: default strict certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//! An owned std container is std's `Vec`/`String` by its exact path, never by the
//! last segment of its type name (OWNED-VEC-NAME-1).
//!
//! `panic_calls::is_owned_slice_container_name` read `tail == "Vec"` on the rendered
//! `Ty::Adt` name, and `guards::owned_container_len_var` read `tail == "String"`.
//! Those gates admit facts that hold for std's container alone: the `is_empty` guard
//! fact `coll_len(w) > 0` and the `Vec` index-bound length `coll_len(w)`, both on the
//! ROOT the receiver traces to. A user type named `Vec` or `String` reaches std's
//! methods through its OWN `Deref`, and the one below returns a different field on
//! each call. So `h2`'s guard read one container and its `len` another, and `k`'s
//! guard bounded a `Vec` that the index never read.
//!
//! BEFORE (stage 1 of `38e6c69b1c`, `scratchpad/stage1-w11fix`; each revision's flags
//! with `--emit=metadata`, 2026-10-04): default and strict exit 0, and none of the
//! annotations below fires. `h2`, `fld` and `s2` read `overflow:sub proved` with the
//! overflow check elided (`TRUST_ELIDE_DEBUG=1`: `elided 1`) under all three
//! revisions. `k` read `slice proved` (ay-in-process); its runtime-checked `assert`
//! row gave the only diagnostics, two warnings under default and strict and two
//! errors under certify (so certify exits 1 on `k` alone). The same code under
//! another name, `owned_vec_name_requires_std_vec_wrap_control.rs`, is refused by
//! every revision (`overflow:sub` FAILED, the `slice` row unknown).
//!
//! AFTER (predicted, then measured): both tests take the exact std path
//! (`alloc::vec::Vec`/`std::vec::Vec`, `alloc::string::String`/`std::string::String`).
//! A user `Vec`/`String` then mints no root length, so each user function reads what
//! its renamed twin reads today. The annotations were derived on the BEFORE compiler
//! from a twin of this file whose user types are renamed (`Vec` to `Wrap2`, `String`
//! to `SWrap2`, nothing else changed): under each revision that twin printed exactly
//! the errors annotated here, at these lines, and no warning. They leave out
//! obligation counts, which DEREF-ANCHOR-1 (the `Deref` hop these shapes also ride)
//! may change without changing the verdict. Measured on the stage 1 of `ee3f51541d`
//! (2026-10-04, which carries DEREF-ANCHOR-1 too): every annotation fires in every
//! revision and nothing else is reported; `k`'s `slice` row reads failed.
//!
//! The std controls `h2_std`, `s2_std` and `fld_std` stay proved, unannotated (each
//! `elided 1` before): std's `Vec` is the extractor's `Seq`, and std's `String` is
//! `alloc::string::String` (both measured with `-Ztrust-dump`).

use std::cell::Cell;

/// A user type NAMED `Vec`, whose `Deref` alternates two different std `Vec`s.
pub struct Vec {
    pub a: std::vec::Vec<u32>,
    pub b: std::vec::Vec<u32>,
    pub flip: Cell<bool>,
}

impl core::ops::Deref for Vec {
    type Target = std::vec::Vec<u32>;
    fn deref(&self) -> &std::vec::Vec<u32> {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn h2(w: &Vec) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec::h2`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec::h2`
    if w.is_empty() {
        return 0;
    }
    w.len() - 1
}

pub fn k(w: &Vec, i: usize) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec::k`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec::k`
    if i < w.len() { w[i] } else { 0 }
}

/// The same user `Vec`, held in a struct field (the field-place arm).
pub struct Fld {
    pub v: Vec,
}

pub fn fld(f: &Fld) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec::fld`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec::fld`
    if f.v.is_empty() {
        return 0;
    }
    f.v.len() - 1
}

/// A user type NAMED `String`, whose `Deref` alternates two different std `String`s.
pub struct String {
    pub a: std::string::String,
    pub b: std::string::String,
    pub flip: Cell<bool>,
}

impl core::ops::Deref for String {
    type Target = std::string::String;
    fn deref(&self) -> &std::string::String {
        let f = self.flip.get();
        self.flip.set(!f);
        if f { &self.b } else { &self.a }
    }
}

pub fn s2(w: &String) -> usize {
    //~^ ERROR Trust Level 0 safety verification incomplete for `owned_vec_name_requires_std_vec::s2`
    //~| ERROR Trust strict verification failed for `owned_vec_name_requires_std_vec::s2`
    if w.is_empty() {
        return 0;
    }
    w.len() - 1
}

/// Control: std's own `Vec` (the extractor's `Seq`) keeps the `is_empty` fact.
pub fn h2_std(v: &std::vec::Vec<u32>) -> usize {
    if v.is_empty() {
        return 0;
    }
    v.len() - 1
}

/// Control: std's own `String` (`alloc::string::String`, exact path) keeps it.
pub fn s2_std(v: &std::string::String) -> usize {
    if v.is_empty() {
        return 0;
    }
    v.len() - 1
}

/// Control: a std `Vec` field keeps the field-place fact.
pub struct FldStd {
    pub v: std::vec::Vec<u32>,
}

pub fn fld_std(f: &FldStd) -> usize {
    if f.v.is_empty() {
        return 0;
    }
    f.v.len() - 1
}
