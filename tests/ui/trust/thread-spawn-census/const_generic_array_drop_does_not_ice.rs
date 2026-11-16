//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Znext-solver=globally --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census -Znext-solver=globally --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A const-generic array of a non-`Copy` type moved by value. The spawn
//! census asks `needs_drop` for `[Result<(), String>; N]` under an env that
//! carries no `ConstArgHasType` clause for `N`; the new trait solver used to
//! panic in `find_const_ty_from_env` instead of answering, ICEing every
//! compile of a crate containing this shape. The census now answers
//! conservatively (needs drop) when the env cannot type a const the type
//! mentions. Pinned to `-Znext-solver=globally` (the production solver mode
//! this ICE fired in); the coherence-mode census failures are a separate
//! pre-existing port breakage.

#![allow(dead_code)]

fn take<const N: usize>(a: [Result<(), String>; N]) {
    let _b = a;
}

pub fn use_it() {
    take::<3>([Ok(()), Ok(()), Ok(())]);
}
