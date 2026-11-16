//@ revisions: reduce_o0
//@ revisions: capture_call_o0 size_of_fnptr_o0 size_of_fnptr_o0_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_callee_inlinable_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[size_of_fnptr_o0_certify] compile-flags: -Ztrust-policy=certify
//@[reduce_o0] check-fail
//@[capture_call_o0] check-pass
//@[size_of_fnptr_o0] check-pass
//@[size_of_fnptr_o0_certify] check-pass
//@ rustc-env:TRUST_VANILLA_DEBUG=1
//@[capture_call_o0] forbid-output: [CALLABLE_TYPE_ARG]
//@[size_of_fnptr_o0] forbid-output: [CALLABLE_TYPE_ARG]
//@[size_of_fnptr_o0_certify] forbid-output: [CALLABLE_TYPE_ARG]
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! The ADT residual of the fn-pointer `requires` fix (docs/KNOWN_HAZARDS.md, "FIX
//! PREPARED 2026-09-30 … an item owing a `requires` inside a type argument"): under
//! an explicit `-Zmir-opt-level=2` the MIR inliner folds `once(y).map(add1)` into a
//! `Map` aggregate and leaves the call that consumes it, so `add1` is a generic
//! argument of an ADT, not of any call: `reduce` becomes
//! `<Map<Once<u32>, fn(u32) -> u32 {add1}> as Iterator>::reduce::<{closure@…}>` (a
//! local closure), `max()` the same `Self` with core's `max_by` closure, `collect`
//! `SpecFromIterNested::<u32, Map<…, fn(u32) -> u32 {add1}>>::from_iter`, and a
//! local generic consumer `run::<Map<Once<u32>, fn(u32) -> u32 {add1}>>`. `add1`
//! runs inside the callee, and the callable type-argument gate took an ADT as
//! resolved whatever it wrapped.
//!
//! BEFORE (a stage 1 of `fbc6068e3`, measured 2026-09-30 by compiling each revision
//! as compiletest does). LIVE through a consumer nobody verifies: `run` below carries
//! `#[trust::assume_total]`, and `at_o3`/`at_o3_certify` built exit 0 with no
//! `[CALLABLE_TYPE_ARG]` line (strict too, and `dep_at_o3_memory_safe` exit 0); the
//! same `f` built verify-on under certify with `-Coverflow-checks=on` and linked into
//! a verify-off `main` RETURNED `f(u32::MAX) = Some(0)`, where the verify-off build of
//! it panics "attempt to add with overflow". (`dep_*_memory_safe` exit 0 says nothing
//! about the gate on that stage 1, which has no L2; with L2 the gate answers the same
//! "resolved" for them — predicted.) That is not the declared `assume_total` route
//! (an `assume_total` body calling `add1` itself): `run` names no `requires` item,
//! and `run2(add1, y)` into an `assume_total` `run2<F: Fn(u32) -> u32>` is refused
//! by the gate at the same flags. `reify_o3`, `dep_reify_o3_memory_safe`, `ptr_o3`,
//! `ptr_o3_certify` and `ptr_by_value_o3` built exit 0 the same way (`ptr_*` hand
//! `run` a POINTER to `add1`, `run::<Map<Once<u32>, fn(u32) -> u32>>`). MASKED
//! through std consumers:
//! every `reduce`/`max`/`collect` revision was refused, but at `-Zmir-opt-level=2`
//! only by unrelated rows — for `reduce` and `dep_reduce` the runtime-checked
//! panic-freedom row of the `reduce` call, kept fatal as a generic absent callee; for
//! `collect` that row and five `unsupported_mir` rows; for `max` the native lowering
//! failing on `max_by`'s capturing closure; for `dyn_o3` two `unsupported_mir` rows
//! for the unsizing cast; for `fnlocal_m0` the lowering's `Call(indirect)` — with no
//! `requires` note and no `[CALLABLE_TYPE_ARG]` line; the `reduce`/`max` twins were
//! refused by the same rows. `reduce_o0` (the `map(add1)` call survives at `-O0`) was
//! refused by the gate with the note. Every check-pass revision compiled. So each
//! positive revision failed this fixture: on its missing error (the live ones) or on
//! its missing note and pins.
//!
//! AFTER (predicted; no stage 1 with these rules was built), three rules of the
//! indirect-call gate (`trust_verify/uncharged_callable.rs`): (1) a type argument of
//! a call, `Self` included, that carries a function item owing a `requires` anywhere
//! inside it is unresolved, and so is the reified-constant carve-out's item when its
//! type arguments carry one (`reify_o3`); (2) a body that CASTS a value carrying such
//! an item to a fn pointer or a `dyn` is refused where the pointer is minted (`ptr_*`,
//! `dyn_o3`); (3) a call through a LOCAL holding a function item has its type
//! arguments asked like a constant's (`fnlocal_m0`). `max` and `fnlocal_m0` are still
//! refused by their lowering failures first, and that error now carries the gate's
//! notes. PINNED under `TRUST_VANILLA_DEBUG=1`: rule (1) prints `[CALLABLE_TYPE_ARG]
//! `<item>` owes its caller a `requires` and is carried inside a type argument`, rule
//! (2) `… and is cast to a fn pointer or a `dyn``, and the gate `[CALLABLE_TYPE_ARG]
//! unresolved` for a direct call's type argument it refuses. Each positive revision
//! requires the lines its route prints (a `~? RAW` annotation; `reduce_o0` only the
//! gate's, its `map(add1)` being refused as an item first). The twins, the capturing
//! closure and the fn-pointer controls forbid every `[CALLABLE_TYPE_ARG]` line, so a
//! revision a rule newly refused could not pass. In `ptr_by_value_o3` only `f`, which
//! mints the pointer, is refused: `hand`, which receives it as a parameter, is not
//! reached by any rule (the module doc's "Not reached").
//!
//! The controls: `size_of::<Option<fn(u32) -> u32>>()` hands the gate a fn POINTER
//! as data, which no rule matches (at `-O0`, where the call survives; at
//! `-Zmir-opt-level=2` it folds to a constant). `capture_call_o0` is rule (1)'s one
//! carve-out: a LOCAL closure that captures `add1` itself and calls it, `c(y)` being
//! `<{closure} as Fn<(u32,)>>::call` — the closure's own body charges that call
//! (its unguarded twin is refused `[precond] FAILED`, measured), so the capture is
//! not walked.
//!
//! W4 ITER-HOF (merged onto this fixture 2026-10-03; measured on stage 1 of the branch
//! `5086736f8` = W4 + origin/main `990826872e`, against stage 1 of `990826872e`
//! itself): W4 credits a requires-FREE local fn item handed to core's iterator
//! adaptors, so core's bundled `Map<Once<u32>, fn(u32) -> u32 {add1}>` members are
//! now vanilla where `add1` is the total twin (`[VANILLA_ROW] NOT-VANILLA callee=`
//! `<Map<…> as Iterator>::next` on `990826872e`, gone with W4), and the native
//! lowering of `max_by`'s fold completes. Three verdicts moved, none of them a gate
//! verdict: `reduce_twin_o3` now builds (rc=0 under the default policy, its one row
//! the `reduce` call's runtime-checked `[assert]`; `reduce_twin_o3_certify` still
//! refuses that row); `max_twin_o3`/`_certify` are still refused, now by the strict
//! lane (the runtime-checked row plus an `unsupported_mir` row for `max_by::fold`'s
//! capturing closure constant) instead of the lowering failure; and `max_o3`/
//! `_certify` are still refused with the gate's `[CALLABLE_TYPE_ARG]` lines and the
//! `add1 … requires` note, now on the strict-lane error (the lowering no longer
//! fails, so its "the indirect-call gate refuses this function as well" note has no
//! error to ride on). The twins are total (`wrapping_add`, `^`), so the new pass is
//! not an accept of a panicking program.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

#[cfg(reduce_o0)]
pub fn f(y: u32) -> Option<u32> {
    //[reduce_o0]~^ ERROR Trust strict verification failed for `requires_callee_inside_adt_type_argument::f`
    //[reduce_o0]~| NOTE add1` carries a `requires` its callers owe
    core::iter::once(y).map(add1).reduce(|a, b| a ^ b)
}

#[cfg(capture_call_o0)]
pub fn f(y: u32) -> u32 {
    let g = add1;
    let c = move |x: u32| if x < 100 { g(x) } else { 0 };
    c(y)
}

#[cfg(any(size_of_fnptr_o0, size_of_fnptr_o0_certify))]
pub fn f() -> usize {
    core::mem::size_of::<Option<fn(u32) -> u32>>()
}

//[reduce_o0]~? RAW [CALLABLE_TYPE_ARG] unresolved
