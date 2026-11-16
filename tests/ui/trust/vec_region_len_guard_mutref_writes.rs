//@ revisions: cleared truncated opaque_call join_len join_remove
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! **The `Vec` region facts stop where `v` may change, and hold only on their own
//! edge (MUTREF-VEC-LEN-GUARD-REFUTE-1 and VEC-REGION-JOIN-SEED-1, Trust 2026-10-12).**
//!
//! The twins of `vec_region_len_guard_mutref.rs`. Each revision holds ONE function, so
//! its exit status is that function's verdict. Each must stay refused under the default
//! policy.
//!
//!  * `cleared`, `truncated`, `opaque_call`: `v.clear()`, `v.truncate(0)` or an opaque
//!    `f(v)` between the guard and `v.len() - 1`. Each hands `v` itself (`copy _1`) to
//!    the callee, so its block is in `Mut(v)` and the later `len` is outside the region:
//!    no `_n == L0` is minted for it (the guard's own `_e <=> L0 == 0` now is, and
//!    constrains nothing the row reads). BEFORE: exit 1, the `- 1` row unknown.
//!  * `join_len`: `let n = if c { v.len() } else { 100 }; v.len() - n`. rustc's
//!    `SimplifyCfg` returns the first `len` straight into the join the `else` arm also
//!    enters with `n == 100`. The facts are seeded as ENTRY facts of the call's return
//!    target, so `n == L0` would hold there on the `else` edge too, and the row would
//!    prove although `c == false` with `v.len() < 100` panics. A fact is now minted only
//!    when the call's block is the target's sole predecessor. BEFORE: exit 1
//!    (`[overflow:sub] FAILED`; no facts were minted without a mutator). This revision
//!    pins the gate against the widening.
//!  * `join_remove`: the same, with a later guarded `v.remove(r)`. The remove switched
//!    the facts on BEFORE this change, so this is the pre-existing false proof the gate
//!    closes: BEFORE, exit 0 with `[overflow:sub] proved` (default policy; the row was
//!    not kernel-certified and its check was kept, so the binary panics as vanilla
//!    does).
//!
//! BEFORE measured with each revision's flags plus `-Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata` on the stage 1 of
//! `46e9afaf95` (main + waves 18 and 19, `scratchpad/stage1-w25probe`, 2026-10-12).
//! AFTER (predicted; not built in the lane): every revision exits 1; `join_remove`'s
//! `- n` row is refuted (`c == false`, `n == 100`).

#[cfg(opaque_call)]
#[inline(never)]
pub fn f(v: &mut Vec<u8>) {
    v.clear()
}

#[cfg(cleared)]
pub fn cleared(v: &mut Vec<u8>) -> usize {
    if !v.is_empty() {
        v.clear();
        v.len() - 1
    } else {
        0
    }
}

#[cfg(truncated)]
pub fn truncated(v: &mut Vec<u8>) -> usize {
    if !v.is_empty() {
        v.truncate(0);
        v.len() - 1
    } else {
        0
    }
}

#[cfg(opaque_call)]
pub fn opaque_call(v: &mut Vec<u8>) -> usize {
    if !v.is_empty() {
        f(v);
        v.len() - 1
    } else {
        0
    }
}

#[cfg(join_len)]
pub fn join_len(v: &mut Vec<u8>, c: bool) -> usize {
    let n = if c { v.len() } else { 100 };
    v.len() - n
}

#[cfg(join_remove)]
pub fn join_remove(v: &mut Vec<u8>, c: bool) -> usize {
    let n = if c { v.len() } else { 100 };
    let r = v.len() - n;
    if r < v.len() {
        v.remove(r);
    }
    r
}
