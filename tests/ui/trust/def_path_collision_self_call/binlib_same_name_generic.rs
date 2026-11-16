//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`: the aux's crate NAME is its file stem, which is this crate's name too:
// Cargo's bin+lib layout, where a package's bin links its own lib.
//@ aux-crate: other=binlib_same_name_generic.rs
//@ compile-flags: --crate-type lib -Ztrust-verify=on -Cmetadata=bin
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 3 (2026-10-07) — the GENERIC form of
//! `binlib_same_name_monomorphic.rs`: a call into the other same-rendering impl is not
//! a self call.
//!
//! Here the call carries generic arguments (`Self = W<T>` and `G`). Round 2 tagged a
//! call's arguments only when they named a NON-local crate whose name another crate
//! shares, so `W<T>` with this crate's own `T` stayed untagged, and the call rendered
//! as the caller's own path plus a turbofish: MEASURED on the round-2 stage 1
//! (`-Ztrust-verify-level=2`, JSON), a PROVED "recursion measure `n` may not decrease"
//! row on the first `f` (the preview3 stage 1 tagged every generic call of a
//! duplicate-name graph and minted none). Round 3 tags a local type too when an extern
//! shares the crate's name, AND gates every direct self call on the compiler's
//! `DefId`-decided self-call blocks; either alone withdraws the row. MEASURED by hand on
//! the round-3 stage 1 (`-Ztrust-verify=on`): the count annotated below, no termination
//! row (preview3 reports the same count here).
//!
//! WHAT THIS FILE PINS (round 5, 2026-10-08, after review): it passes on main (the
//! preview3 stage 1) and on every round since 3, so it cannot fail on main; and because
//! (A) the `DefId` gate and (B) the local-crate argument tag EACH withdraw the row, it
//! turns red only when BOTH are reverted (round 2's state). It pins neither alone. (B)
//! alone is pinned where no compiler frame carries (A)'s set:
//! `crates/trust-mir-extract/tests/generic_args_local_shared_crate_name_tag.rs`
//! (`the_tag_alone_withholds_the_descent_row_without_compiler_context`). (A) alone is
//! pinned by `binlib_same_name_monomorphic.rs`, whose call carries no argument to tag.

pub struct T;
pub struct W<X>(pub X);
pub trait Tr {
    fn f<G: Copy>(n: u64, g: G) -> u64;
}

impl Tr for W<other::T> {
    fn f<G: Copy>(n: u64, g: G) -> u64 {
        //~^ NOTE 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
        if n == 0 {
            return 0;
        }
        <W<T> as Tr>::f::<G>(n - 1, g)
    }
}

impl Tr for W<T> {
    fn f<G: Copy>(n: u64, _g: G) -> u64 {
        let mut k = n;
        while k != 7 {
            k = k.wrapping_add(2);
        }
        k
    }
}
