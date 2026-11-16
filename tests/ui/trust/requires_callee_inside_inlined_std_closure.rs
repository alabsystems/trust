//@ revisions: once_last_o0 once_last_twin_o0
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[once_last_o0] check-fail
//@[once_last_twin_o0] check-pass
//@[once_last_o0] rustc-env:TRUST_VANILLA_DEBUG=1
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Residual L1 of the fn-pointer `requires` fix (docs/KNOWN_HAZARDS.md, the
//! 2026-09-30 entry on "the fn-pointer `requires` residuals"): under an explicit
//! `-Zmir-opt-level=2` the MIR inliner folds `core::iter::once(y).map(div10).last()`
//! into ONE call, `<Once<u32> as Iterator>::fold::<Option<u32>,
//! {closure@map_fold<u32, u32, Option<u32>, fn(u32) -> u32 {div10}, …>}>`, so the
//! `requires`-carrying `div10` is a generic argument of core's closure, not a type
//! argument of any call in the body, and the callable type-argument gate took
//! every sysroot closure as resolved.
//!
//! BEFORE (a stage 1 of `3c29e31164`, measured 2026-09-30 by compiling each
//! revision as below): every check-fail revision here was refused (exit 1), but
//! at `-Zmir-opt-level=2` only by the unrelated `unsupported MIR Const::Closure`
//! row ("capturing closure constant … must be represented as an aggregate"), the
//! same row the `requires`-free `add10` twins get, and with no `requires` note:
//! the day that closure lowers, `once_last_o3`, `fold_o3` and `slice_last_o3`
//! (two nested std closures, `copy_fold` around `map_fold`) are false accepts.
//! `once_last_o0` — `map(div10)` stays a call there — was refused with the note,
//! and `once_last_twin_o0` compiled.
//!
//! AFTER: a SYSROOT closure handed to a call is asked through its parent's type
//! arguments and its upvars, each as a type argument of the call would be
//! (`uncharged_callable`): these `-Zmir-opt-level=2` spellings, whose closure-bearing
//! call survives the inliner, are refused by the gate the `-O0` spelling meets, with
//! the note naming `div10`. (Where the inliner would ERASE the call instead —
//! `Some(y).map(div10)` at the same flags — a verifying session's inliner now keeps
//! it, prepared and not built: docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-09-30 … —
//! under an explicit `-Zmir-opt-level=2` …", and
//! `requires_callee_erased_by_mir_inliner.rs`.) The twins, and a local closure making
//! a guarded DIRECT call (`guarded_closure_o3`), are unchanged: they stay refused at
//! `-Zmir-opt-level=2` for the `Const::Closure` gap (since that rule the closure
//! keeps its guarded `div10(x)` call, charged and proved, where it used to inline
//! `div10`, and `f` also carries a `runtime_checked` panic-freedom row; predicted).
//!
//! PINNED, not just claimed: the gate's refusal and the `Const::Closure` refusal share
//! the generic `Trust strict verification failed` header on this lane, so a twin that
//! the gate newly refused would still match its annotation. Under
//! `TRUST_VANILLA_DEBUG=1` the gate prints `[CALLABLE_TYPE_ARG] unresolved `<ty>`` for
//! the type argument it refuses on; the twins forbid that line, and `once_last_o0`
//! (measured) and `once_last_o3` require it (a `~? RAW` annotation: compiletest reads
//! every non-JSON stderr line as a RAW diagnostic, so an `error-pattern` on it is
//! refused), so the pin is known to fire.

#[cfg(not(once_last_twin_o0))]
pub fn div10(x: u32) -> u32
    requires x != 0
{
    100 / x
}

#[cfg(once_last_twin_o0)]
pub fn add10(x: u32) -> u32 {
    x.wrapping_add(10)
}

#[cfg(once_last_o0)]
pub fn f(y: u32) -> Option<u32> {
    //[once_last_o0]~^ ERROR Trust strict verification failed for `requires_callee_inside_inlined_std_closure::f`
    //[once_last_o0]~| NOTE `div10` carries a `requires` its callers owe
    core::iter::once(y).map(div10).last()
}
//[once_last_o0]~? RAW [CALLABLE_TYPE_ARG] unresolved

#[cfg(once_last_twin_o0)]
pub fn f(y: u32) -> Option<u32> {
    core::iter::once(y).map(add10).last()
}
