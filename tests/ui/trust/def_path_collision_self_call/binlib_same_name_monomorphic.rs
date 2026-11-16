//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`: the aux's crate NAME is its file stem, which is this crate's name too:
// Cargo's bin+lib layout, where a package's bin links its own lib.
//@ aux-crate: other=binlib_same_name_monomorphic.rs
//@ compile-flags: --crate-type lib -Ztrust-verify=on -Cmetadata=bin
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! ARGS-FINGERPRINT-READ-1 round 3 (2026-10-07) — A RENDERED DEF PATH IS NOT AN
//! IDENTITY: two local impls can render ONE, and a call into the OTHER impl is not a
//! self call.
//!
//! `impl Tr for W<other::T>` and `impl Tr for W<T>` both render
//! `<binlib_same_name_monomorphic::W<binlib_same_name_monomorphic::T> as …::Tr>::f`: the
//! lib and this crate share a name, and the printer stamps no crate identity inside a
//! self type. The call below runs the SECOND impl (which loops forever for an even `n`),
//! yet the direct-self termination lane compared rendered paths and read it as a self
//! call, so the non-recursive caller got a PROVED "recursion measure `n` may not
//! decrease" row. The call is monomorphic: it carries no generic argument the
//! duplicate-crate-name tag could mark.
//!
//! Round 3: the compiler hands vcgen the call blocks that may run THIS body, decided
//! from `DefId`s (`direct_self_call_identity_blocks`), and the self-call test ANDs it
//! with the path comparison. MEASURED 2026-10-07 by hand on this shape
//! (`-Ztrust-verify=on`): the preview3 stage 1 (main `7be75e9a80`) reports
//! `2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3` on the
//! first `f` (the termination row is the extra proved one); the round-3 stage 1 reports
//! the count annotated below, with no termination row.

pub struct T;
pub struct W<X>(pub X);
pub trait Tr {
    fn f(n: u64) -> u64;
}

impl Tr for W<other::T> {
    fn f(n: u64) -> u64 {
        //~^ NOTE 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
        // RE-PINNED 2026-10-15 (the merge of 2026-10-14): the call into the SECOND impl is
        // now proved panic-free (that body cannot panic: `wrapping_add` in a loop), so the
        // file builds; still two obligations and no termination row, this file's subject.
        if n == 0 {
            return 0;
        }
        <W<T> as Tr>::f(n - 1)
    }
}

impl Tr for W<T> {
    fn f(n: u64) -> u64 {
        let mut k = n;
        while k != 7 {
            k = k.wrapping_add(2);
        }
        k
    }
}
