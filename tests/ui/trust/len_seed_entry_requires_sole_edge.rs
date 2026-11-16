//@ revisions: join_shared last_dup last_redef controls
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[join_shared] check-fail
//@[last_dup] check-fail
//@[last_redef] check-fail
//@[controls] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! **A collection-length fact holds on one edge and is read on every edge into the
//! block it is seeded at (LEN-TIE-JOIN-SEED-1 and LAST-SOME-ARM-SEED-1, Trust
//! 2026-10-12).**
//!
//! `guards::slice_last_some_nonempty_definitions` seeds `_len == coll_len(v)` (and the
//! view, `to_vec` and `clone` ties) at a call's return target, and `coll_len(v) >= 1` at
//! the `Some` arm of a switch on `v.last()`/`v.first()`. A seeded fact is an ENTRY fact
//! of its block, read on every edge into it. Each revision below holds ONE function, a
//! panicking program the BEFORE compiler accepted:
//!
//!  * `join_shared`: `let n = if c { v.len() } else { 100 }; v.len() - n` over `&Vec`.
//!    rustc's `SimplifyCfg` returns the first `len` straight into the join the `else` arm
//!    also enters with `n == 100`, so `n == coll_len(v)` was read there too and the row
//!    was `proved`. It panics for `c == false`, `v.len() < 100` (the row was not
//!    kernel-certified, so the check was kept).
//!  * `last_dup`: `match v.last() { Some(_) => {}, None => {} }; v.len() - 1`. rustc -O0
//!    spells the match `switchInt(d) -> [0: bbJ, 1: bbJ, ..]`: the `Some` target is the
//!    join `None` also enters. The row was kernel-certified, its overflow check ELIDED,
//!    and the binary returned `usize::MAX` for an empty `v` (the run twin is
//!    `len_seed_entry_requires_sole_edge_run.rs`).
//!  * `last_redef`: `let mut o = v.last(); if c { o = Some(&5); } match o { Some(_) =>
//!    v.len() - 1, .. }`: once `o` is reassigned its `Some` says nothing about `v`.
//!
//! A tie is now seeded only when the call's block is the target's sole predecessor, and
//! the non-emptiness fact only when the `Some` edge is the arm's only entry
//! (VARIANT-ARM-DUP-EDGE-1's per-edge relation) and the `Option` local has one
//! definition in the body, that call, with no `&mut`/raw escape.
//!
//! `controls` holds the shapes the facts exist for (`match v.last() { Some(_) =>
//! v.len() - 1, .. }`, `if let Some(_) = v.last()`, `if v.len() > 0 { v.len() - 1 }`).
//!
//! BEFORE: every revision exits 0, each function's `- 1`/`- n` row `proved`, measured
//! with each revision's flags plus `-Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata` on the stage 1 of `46e9afaf95` (main + waves 18 and 19,
//! `scratchpad/stage1-w25probe`, 2026-10-12). AFTER (predicted; not built in the lane):
//! the three lie revisions exit 1 with that row refuted, and `controls` exits 0.

#[cfg(join_shared)]
pub fn join_shared(v: &Vec<u8>, c: bool) -> usize {
    let n = if c { v.len() } else { 100 };
    v.len() - n
}

#[cfg(last_dup)]
pub fn last_dup(v: &Vec<u8>) -> usize {
    match v.last() {
        Some(_) => {}
        None => {}
    }
    v.len() - 1
}

#[cfg(last_redef)]
pub fn last_redef(v: &Vec<u8>, c: bool) -> usize {
    let mut o = v.last();
    if c {
        o = Some(&5);
    }
    match o {
        Some(_) => v.len() - 1,
        None => 0,
    }
}

#[cfg(controls)]
pub fn last_ok(v: &Vec<u8>) -> usize {
    match v.last() {
        Some(_) => v.len() - 1,
        None => 0,
    }
}

#[cfg(controls)]
pub fn last_iflet(v: &Vec<u8>) -> usize {
    if let Some(_) = v.last() { v.len() - 1 } else { 0 }
}

#[cfg(controls)]
pub fn len_guard_shared(v: &Vec<u8>) -> usize {
    if v.len() > 0 { v.len() - 1 } else { 0 }
}
