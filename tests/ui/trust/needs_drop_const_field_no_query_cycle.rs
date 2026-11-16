//@ revisions: plain plain_lower opaque opaque_lower
//@ needs-trust-verify
//@ build-pass
//@ edition: 2021
//@[plain] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[plain_lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@[opaque] compile-flags: --crate-type=lib -Ztrust-verify=on -Ztrust-policy=advisory
//@[opaque_lower] compile-flags: --crate-type=lib -Ztrust-verify=off -Ztrust-ir-lower=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **Regression (fix11, CTFE-IN-MIR-BUILT-1): `needs_drop` of a local struct whose FIELD names a
//! constant that is not leaf must not evaluate it from inside `mir_built`.**
//!
//! Building `h4`'s MIR, the producer's drop planner (`drops::plan_body` ->
//! `cycle_safe_needs_drop`) asks whether `W4` needs drop. `W4`'s own flags show no constant;
//! its field `[u8; h4()]` does, and both ways of answering normalized that field, which
//! evaluates `h4()`, whose MIR is the one being built:
//!
//! * in a crate that declares an opaque (`opaque*`: the RPIT below), the leak-free walk
//!   (`ctfe_reentrancy::needs_drop_leak_free`) normalized it with `try_normalize_leak_free`;
//! * in one that declares none (`plain*`), rustc's own `needs_drop_raw` normalized it through
//!   `adt_drop_tys`.
//!
//! MEASURED on the stage 1 of `192b4a810f`: `error[E0391]: cycle detected when evaluating
//! type-level constant` in all four revisions (`-Ztreat-err-as-bug=1` shows
//! `needs_drop_leak_free` < `drops::plan_body` for `opaque_lower`, and `needs_drop_raw` <
//! `needs_drop_unrevealed` < `drops::plan_body` for `plain_lower`); stock nightly-2026-04-20
//! compiles the file with the RPIT and without it. A field naming such a constant now answers
//! "may need drop", the planner's fail-closed side, before anything normalizes it
//! (`non_leaf_constant_if_frozen` in the leak-free walk;
//! `needs_drop_may_evaluate_non_leaf_constant` before rustc's query). `build-pass` in every
//! revision is the assertion.

#[cfg(any(opaque, opaque_lower))]
pub fn rpit() -> impl Sized {
    0u8
}

pub struct W4 {
    a: [u8; h4()],
    n: u8,
}

pub const fn h4() -> usize {
    let w: Option<&W4> = None;
    match w {
        Some(r) => r.n as usize,
        None => 1,
    }
}

pub fn w4(x: &W4) -> u8 {
    x.n + x.a.len() as u8
}
