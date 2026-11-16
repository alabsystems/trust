//@ revisions: helper helper_certify helper_memory_safe helper_json unit unit_certify
//@ revisions: ref_arg ref_arg_certify ref_arg_memory_safe slice
//@ revisions: measured measured_certify unbounded mutual
//@ revisions: trait_default bool_arg bool_arg_certify fn_ptr_residual fn_ptr_certify
//@ revisions: fn_ptr_mixed fn_item_hof fn_ptr_residual_codegen
//@ revisions: callee_measured
//@ revisions: unit_l0_certify bool_arg_l0_certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[helper_certify] compile-flags: -Ztrust-policy=certify
//@[unit_certify] compile-flags: -Ztrust-policy=certify
//@[ref_arg_certify] compile-flags: -Ztrust-policy=certify
//@[measured_certify] compile-flags: -Ztrust-policy=certify
//@[bool_arg_certify] compile-flags: -Ztrust-policy=certify
//@[fn_ptr_certify] compile-flags: -Ztrust-policy=certify
//@[unit_l0_certify] compile-flags: -Ztrust-policy=certify -Ztrust-verify-level=0
//@[bool_arg_l0_certify] compile-flags: -Ztrust-policy=certify -Ztrust-verify-level=0
//@[helper_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[ref_arg_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[helper_json] compile-flags: -Ztrust-verify-output=json --error-format=human
//@[helper] build-pass
//@[helper_memory_safe] build-pass
//@[helper_json] build-pass
//@[unit] build-pass
//@[ref_arg] build-pass
//@[slice] build-pass
//@[measured] build-pass
//@[measured_certify] build-pass
//@[bool_arg] build-pass
//@[fn_ptr_residual] check-fail
//@[fn_ptr_residual_codegen] compile-flags: -Ztrust-policy=advisory
//@[fn_ptr_residual_codegen] build-pass
//@[fn_ptr_mixed] build-pass
//@[fn_item_hof] build-pass
//@[callee_measured] build-pass
//@[helper_certify] check-fail
//@[unit_certify] check-fail
//@[ref_arg_certify] check-fail
//@[ref_arg_memory_safe] check-fail
//@[unbounded] check-fail
//@[mutual] check-fail
//@[trait_default] check-pass
//@[bool_arg_certify] check-fail
//@[fn_ptr_certify] check-fail
//@[unit_l0_certify] check-fail
//@[bool_arg_l0_certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[helper_memory_safe] dont-require-annotations: WARN
//@[ref_arg_memory_safe] dont-require-annotations: WARN
//@[ref_arg_memory_safe] dont-require-annotations: ERROR
//@[mutual] dont-require-annotations: WARN
//@[trait_default] dont-require-annotations: WARN
//@[trait_default] dont-require-annotations: ERROR
//@[bool_arg] dont-require-annotations: WARN
//@[bool_arg_certify] dont-require-annotations: ERROR
//@[fn_ptr_residual] dont-require-annotations: WARN
//@[fn_ptr_residual_codegen] dont-require-annotations: WARN
//@[fn_ptr_mixed] dont-require-annotations: WARN
//@[fn_item_hof] dont-require-annotations: WARN
//@[callee_measured] dont-require-annotations: WARN
//@[measured] forbid-output: termination is ASSUMED
//@[measured_certify] forbid-output: termination is not established
//@[unbounded] forbid-output: termination is ASSUMED
//@[mutual] forbid-output: termination is ASSUMED
//@[helper_json] forbid-output: termination is ASSUMED
//[unit_l0_certify]~? ERROR -Ztrust-policy=certify requires -Ztrust-verify-level=1 or 2
//[bool_arg_l0_certify]~? ERROR -Ztrust-policy=certify requires -Ztrust-verify-level=1 or 2
//! D9 (ruled 2026-09-27, owner-delegated; docs/DECISION_QUEUE.md "D9"): direct
//! SELF recursion that no `decreases` measure covers is charged as an
//! `assumption:termination-unmeasured` row — CONDITIONAL on the default lane
//! (a warning, and a skipped row the Gate line counts), admitted by memory-safe,
//! refused under `-Ztrust-policy=certify`.
//!
//! BEFORE (pack `5ab8dcccfcb`, measured): `helper` and `unit` built rc 0 on the
//! default lane AND under certify with "1 proved … out of 1 obligation(s)" and
//! no `[termination]` row at all; the binaries overflow the stack (134).
//! `ref_arg`/`slice` built rc 0 with two runtime-checked warnings and no
//! termination row. vcgen's inferred direct-self lane mints its descent rows
//! only when the first integer parameter binds at every self call, every
//! non-self call is a vanilla sysroot routine and there is no loop; otherwise it
//! mints NOTHING (`crates/trust-vcgen/src/termination.rs`).
//!
//! Revisions:
//! * `helper`, `unit`, `ref_arg`, `slice`, `bool_arg` — charged: one skipped row
//!   per self call, a warning, the build passes. `bool_arg` is TERMINATING
//!   (`f(!x)` under `if x`): the documented cost — conditional, not refused, on
//!   the default lane; refused under certify.
//! * `*_certify` — the charge is the refusal (`helper`/`unit`: the ONLY error;
//!   they built rc 0 under certify before).
//! * `helper_memory_safe` — memory-safe admits the row (critique H1: it built
//!   rc 0 there before; refusing would be an unratified capability loss).
//!   `ref_arg_memory_safe` stays refused, for its runtime-checked row, not for
//!   the charge.
//! * `helper_json` — JSON-only output (targo's mode): the row reaches the wire,
//!   no warning, and no `trimmed_def_paths` ICE (critique H5).
//! * `measured`, `measured_certify`, `unbounded` — vcgen made a recursion
//!   statement (proved, or `[termination] UNKNOWN`): exempt, byte-identical
//!   summary line (a charge would read "… 1 skipped out of N+1").
//! * `mutual` — the recursion-SCC lane's rows are unchanged; nothing is added.
//! * `trait_default` — a trait default method calling `self.m(..)`: vcgen's
//!   string identity misses the `<Self as T>::m` self call (no row); the compiler
//!   census resolves it by `DefId` and charges it. It used to be refused on the
//!   strict lane for an unrelated row (the open dispatch `<Self as Walk>::walk`'s
//!   fatal absent-callee row); since OD-1 phase 1 (2026-10-04) that call is an
//!   admitted instance hypothesis, so the lane passes CONDITIONALLY with both
//!   disclosures (the termination charge and the hypothesis row).
//! * `fn_ptr_residual`, `fn_ptr_certify` — `let g: fn(u64) -> u64 = f; g(n)`:
//!   no DIRECT self call. It was the disclosed residual (the revision keeps that
//!   name): before review F5 nothing was charged, and raw certify built it rc 0
//!   with no output (measured on pack `5ab8dcccfcb`). F5 (ruled YES, 2026-09-27)
//!   charges the self REFERENCE — `f` reified to a `fn` pointer — so it is
//!   CONDITIONAL on the default lane and refused under certify (the only error).
//! * `fn_ptr_mixed` — the same pointer plus a direct `f(n / 2)`: both are
//!   charged, the direct call and the reference, in one disclosure.
//! * `fn_item_hof` — the function's own fn item handed to a std higher-order
//!   function (`t.kids.iter().map(size)`): a self reference, charged. BEFORE
//!   (review, measured on pack `5ab8dcccfcb`): exit 0 on the default lane with
//!   one runtime-checked row and two warnings; certify exit 1; the JSON carried
//!   a `native-verification-gap` row for the fold closure — a verification gap,
//!   not a termination statement. No recursion-SCC row covers the reference:
//!   the local call graph records no fn item passed as a value, and `size` is a
//!   singleton component, which Tarjan drops.
//! * `callee_measured` — a measured callee's recursion row does not exempt its
//!   caller (critique H7: only THIS function's rows count).
//! * `unit_l0_certify`, `bool_arg_l0_certify` — `unit_certify`'s and
//!   `bool_arg_certify`'s bodies under `-Ztrust-verify-level=0`. The charge is an
//!   L1 obligation, and the level filter left it out: certify built both exit 0
//!   (MEASURED on stage 1 of `782780ea0d`, each revision compiled directly; the
//!   binary form of `flip` overflowed its stack, exit 134). Since 2026-10-03 the
//!   driver refuses certify at level 0 before any session exists
//!   (docs/DECISION_QUEUE.md "L0-CERTIFY"), so certify refuses unmeasured
//!   recursion at every level it runs at.
//!
//! The `.stderr` output is not checked (`dont-check-compiler-stderr`); the pins
//! are the annotations below. They were written from the implementation's
//! message text before the lane was first built, then MEASURED on its first
//! stage 1 (`22dea9d082b`, 2026-09-27): 22/22 revisions pass (the one fix was
//! `helper_json`'s wire pin, see its comment at the end of the file). Exit codes
//! against the pinned-seed pack `4d9a20e3daf` (the same source without D9),
//! every revision compiled directly: exactly `helper_certify`, `unit_certify`,
//! `bool_arg_certify` and `fn_ptr_certify` change, rc 0 -> 1 (the charge is
//! their only error); the other 18 keep their exit code.

#![allow(unconditional_recursion)]

#[cfg(any(helper, helper_certify, helper_memory_safe, helper_json))]
fn g() -> u64 {
    1
}
#[cfg(any(helper, helper_certify, helper_memory_safe, helper_json))]
pub fn f(n: u64) -> u64 {
    //[helper]~^ WARN termination is ASSUMED, not proved
    //[helper]~| NOTE 0 runtime-checked, 1 skipped out of 2 obligation(s)
    //[helper_memory_safe]~^^^ WARN termination is ASSUMED, not proved
    //[helper_certify]~^^^^ ERROR termination is not established
    let _ = g();
    f(n)
}

#[cfg(any(unit, unit_certify, unit_l0_certify))]
pub fn spin() {
    //[unit]~^ WARN termination is ASSUMED, not proved
    //[unit]~| NOTE 0 runtime-checked, 1 skipped out of 2 obligation(s)
    //[unit_certify]~^^^ ERROR termination is not established
    spin()
}

#[cfg(any(ref_arg, ref_arg_certify, ref_arg_memory_safe))]
pub struct T(pub u32);
#[cfg(any(ref_arg, ref_arg_certify, ref_arg_memory_safe))]
pub fn r(t: &T) -> u32 {
    //[ref_arg]~^ WARN termination is ASSUMED, not proved
    //[ref_arg]~| WARN Trust Level 0 safety verification incomplete
    //[ref_arg]~| WARN 1 obligation(s) were not fully verified
    //[ref_arg]~| NOTE 1 runtime-checked, 1 skipped out of 2 obligation(s)
    //[ref_arg_memory_safe]~^^^^^ WARN termination is ASSUMED, not proved
    //[ref_arg_certify]~^^^^^^ ERROR termination is not established
    //[ref_arg_certify]~| ERROR Trust Level 0 safety verification incomplete
    //[ref_arg_certify]~| ERROR Trust strict verification failed
    r(t)
}

#[cfg(slice)]
pub fn count(v: &[u32]) -> usize {
    //[slice]~^ WARN termination is ASSUMED, not proved
    //[slice]~| WARN Trust Level 0 safety verification incomplete
    //[slice]~| WARN 1 obligation(s) were not fully verified
    //[slice]~| NOTE 1 runtime-checked, 1 skipped out of 4 obligation(s)
    match v {
        [] => 0,
        [_, rest @ ..] => count(rest).saturating_add(1),
    }
}

#[cfg(any(measured, measured_certify))]
pub fn count(n: u32) -> u32 {
    //[measured]~^ NOTE 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
    //[measured_certify]~^^ NOTE 3 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)
    if n == 0 { 0 } else { count(n - 1) }
}

#[cfg(unbounded)]
pub fn r(n: u64) -> u64 {
    //[unbounded]~^ ERROR Trust strict verification failed for
    //[unbounded]~| NOTE 1 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
    r(n.wrapping_add(1))
}

#[cfg(mutual)]
pub fn a(n: u64) -> u64 {
    //[mutual]~^ ERROR Trust strict verification failed for
    //[mutual]~| NOTE 0 proved, 0 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    b(n)
}
#[cfg(mutual)]
pub fn b(n: u64) -> u64 {
    //[mutual]~^ ERROR Trust strict verification failed for
    //[mutual]~| NOTE 0 proved, 0 failed, 1 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    a(n)
}

#[cfg(trait_default)]
pub trait Walk {
    fn walk(&self, n: u64) -> u64 {
        //[trait_default]~^ WARN termination is ASSUMED, not proved
        if n == 0 { 0 } else { self.walk(n - 1) }
    }
}

#[cfg(any(bool_arg, bool_arg_certify, bool_arg_l0_certify))]
pub fn flip(x: bool) -> bool {
    //[bool_arg]~^ WARN termination is ASSUMED, not proved
    //[bool_arg_certify]~^^ ERROR termination is not established
    if x { flip(!x) } else { false }
}

#[cfg(any(fn_ptr_residual, fn_ptr_certify, fn_ptr_residual_codegen))]
pub fn f(n: u64) -> u64 {
    //[fn_ptr_residual]~^ WARN termination is ASSUMED, not proved — 1 self reference(s) take this function as a value
    //[fn_ptr_certify]~^^ ERROR termination is not established — 1 self reference(s) take this function as a value
    //[fn_ptr_residual,fn_ptr_certify]~^^^ ERROR Trust strict verification failed for `self_recursion_termination_unmeasured::f`
    // ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated
    // registry discharges (the reified self reference) publish an `unknown` row; refused.
    // `fn_ptr_residual` was `build-pass`; `fn_ptr_residual_codegen` keeps the codegen of
    // this body covered under `-Ztrust-policy=advisory` (`build-pass`).
    let g: fn(u64) -> u64 = f;
    g(n)
}

#[cfg(fn_ptr_mixed)]
pub fn f(n: u64) -> u64 {
    //[fn_ptr_mixed]~^ WARN 1 self call(s) bind no `decreases` measure, and 1 self reference(s) take this function as a value
    let g: fn(u64) -> u64 = f;
    if n == 0 { g(n) } else { f(n / 2) }
}

#[cfg(fn_item_hof)]
pub struct Tree {
    pub kids: Vec<Tree>,
}
#[cfg(fn_item_hof)]
pub fn size(t: &Tree) -> usize {
    //[fn_item_hof]~^ WARN termination is ASSUMED, not proved — 1 self reference(s) take this function as a value
    t.kids.iter().map(size).fold(1usize, |a, b| a.wrapping_add(b))
}

#[cfg(callee_measured)]
pub struct T(pub u32);
#[cfg(callee_measured)]
pub fn g(n: u64) -> u64 {
    if n == 0 { 0 } else { g(n - 1) }
}
#[cfg(callee_measured)]
pub fn f(t: &T, n: u64) -> u64 {
    //[callee_measured]~^ WARN termination is ASSUMED, not proved
    let _ = g(n);
    f(t, n)
}

// The charge row on the JSON wire. ONE annotation, not two: compiletest lets an
// output line satisfy at most one expected annotation, and the whole
// `function_result` record (kind, outcome and solver alike) is a single line —
// a second `RAW` pin on the same record is never found (measured on the first
// stage-1 build, 2026-09-27). The solver label is minted only on the
// `assumption:termination-unmeasured` row (`termination_unmeasured_row`, whose
// kind the module's unit tests pin), and the reason names the tag.
//[helper_json]~? RAW "outcome":"skipped","solver":"trust-termination-charge","time_ms":0,"reason":"termination assumption `termination-unmeasured`
