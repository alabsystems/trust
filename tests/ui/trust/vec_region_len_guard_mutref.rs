//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! **A length guard on a `&mut Vec` parameter proves the subtraction it guards
//! (MUTREF-VEC-LEN-GUARD-REFUTE-1, Trust 2026-10-12).**
//!
//! `if !v.is_empty() { v.len() - 1 }` over `v: &mut Vec<u8>` is valid Rust that stock
//! rustc builds. The default `trustc` refused it: `[overflow:sub] FAILED
//! (ay-in-process)`, with the counterexample `_2 = false, .., v = 0`, which breaks its
//! own guard. The `&mut`-parameter havoc at the second `Vec::len(&*v)` call severs every
//! tie to the guard, and `guards::owned_container_len_var` declines a `&mut` receiver by
//! design. The one mechanism that survives the havoc, the `Vec` region facts over the
//! fresh constant `__trust_vec_region_len_1` (`_e <=> L0 == 0`, `_n == L0`,
//! `trust-vcgen/src/generate/vec_region.rs`), was minted only for a base a charged
//! `remove`/`swap_remove`/`insert` also used: adding a later `v.remove(r)` made the same
//! subtraction prove. The facts are now minted at every fact site of a region-eligible
//! base. Their argument (`L0` is a constant; nothing in `Mut(v)` ran on any path to the
//! site) never mentioned a mutator, and no premise is added (docs/TCB.md, VEC-INSERT).
//!
//! The same shapes over `&Vec<u8>`, an owned `Vec<u8>`, `&mut [u8]` and `let n =
//! v.len(); if n > 0 { n - 1 }` already proved.
//!
//! BEFORE: every function below except `g` reported `[overflow:sub] FAILED`, and both
//! revisions exited 1, measured with each revision's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata` on the stage 1 of
//! `46e9afaf95` (main + waves 18 and 19, `scratchpad/stage1-w25probe`, 2026-10-12).
//!
//! AFTER (predicted; not built in the lane): both revisions build. `last_elem` is
//! `default` only: its `<Vec<u8> as Index<usize>>::index` call carries a
//! `[trust-absent-callee-assumption]` row that stays runtime-checked (default records it
//! and passes; `certify` refuses it whatever this fix does).
//!
//! The fail-closed twins (a `clear`, a `truncate(0)` or an opaque `f(v)` between the
//! guard and the subtraction, and a `len` returning into a join) are
//! `vec_region_len_guard_mutref_writes.rs`.

#[inline(never)]
pub fn g() {
    std::hint::black_box(0u8);
}

pub fn last_index(v: &mut Vec<u8>) -> usize {
    if !v.is_empty() { v.len() - 1 } else { 0 }
}

pub fn last_index_gt(v: &mut Vec<u8>) -> usize {
    if v.len() > 0 { v.len() - 1 } else { 0 }
}

pub fn ge2(v: &mut Vec<u8>) -> usize {
    if v.len() >= 2 { v.len() - 2 } else { 7 }
}

// A nullary call between the guard and the subtraction mutates nothing of `v`.
pub fn t_unrelated_nomut(v: &mut Vec<u8>) -> usize {
    if !v.is_empty() {
        g();
        v.len() - 1
    } else {
        0
    }
}

#[cfg(default)]
pub fn last_elem(v: &mut Vec<u8>) -> u8 {
    if !v.is_empty() { v[v.len() - 1] } else { 0 }
}
