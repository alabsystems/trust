//@ revisions: fnptr fnptr_copied map_last fnptr_param foreign_twin
//@ revisions: local_twin direct fnptr_default
//@ revisions: skip_fnptr skip_direct skip_let skip_map skip_twin
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_callee_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[fnptr] compile-flags: -Ztrust-policy=memory-safe
//@[fnptr_copied] compile-flags: -Ztrust-policy=memory-safe
//@[map_last] compile-flags: -Ztrust-policy=memory-safe
//@[fnptr_param] compile-flags: -Ztrust-policy=memory-safe
//@[foreign_twin] compile-flags: -Ztrust-policy=memory-safe
//@[local_twin] compile-flags: -Ztrust-policy=memory-safe
//@[direct] compile-flags: -Ztrust-policy=memory-safe
//@[skip_fnptr] compile-flags: -Ztrust-policy=memory-safe
//@[skip_direct] compile-flags: -Ztrust-policy=memory-safe
//@[skip_let] compile-flags: -Ztrust-policy=memory-safe
//@[skip_map] compile-flags: -Ztrust-policy=memory-safe
//@[skip_twin] compile-flags: -Ztrust-policy=memory-safe
//@[fnptr] check-fail
//@[fnptr_copied] check-fail
//@[map_last] check-fail
//@[fnptr_param] check-fail
//@[foreign_twin] check-fail
//@[local_twin] check-fail
//@[direct] check-fail
//@[fnptr_default] check-fail
//@[skip_fnptr] check-fail
//@[skip_direct] check-fail
//@[skip_let] check-fail
//@[skip_map] check-fail
//@[skip_twin] check-fail
//@[fnptr_param] forbid-output: carries a `requires`
//@[foreign_twin] forbid-output: carries a `requires`
//@ dont-check-compiler-stderr
//@[fnptr] dont-require-annotations: ERROR
//@[fnptr_copied] dont-require-annotations: ERROR
//@[map_last] dont-require-annotations: ERROR
//@[fnptr_param] dont-require-annotations: ERROR
//@[foreign_twin] dont-require-annotations: ERROR
//@[direct] dont-require-annotations: ERROR
//@[fnptr_default] dont-require-annotations: ERROR
//@[skip_fnptr] dont-require-annotations: ERROR
//@[skip_direct] dont-require-annotations: ERROR
//@[skip_let] dont-require-annotations: ERROR
//@[skip_map] dont-require-annotations: ERROR
//@[skip_twin] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Residual L2 of the fn-pointer `requires` fix (docs/KNOWN_HAZARDS.md, the
//! 2026-09-30 entry on "the fn-pointer `requires` residuals"): under
//! `-Ztrust-policy=memory-safe`, a `requires`-carrying function of ANOTHER crate
//! reached with no call site to charge its clause must be refused, as strict, the
//! default policy and certify refuse it.
//!
//! `dep::add1` (`auxiliary/requires_callee_dep.rs`, verified on the default policy)
//! is verified UNDER `requires x < 100`, and its overflow check is elided on the
//! strength of it. The memory-safe lane never asked the indirect-call gate
//! (`function_has_unresolved_indirect_call`): it judges ROWS, and an unresolved
//! indirect call has none. In one crate the `requires` function's own
//! `assumption:requires` row happened to refuse the build; across crates that row
//! is in the callee's crate, built under another policy.
//!
//! BEFORE (a stage 1 of `3c29e31164`, measured 2026-09-30 by compiling each
//! revision as below; the verify-off `main` is the probe of the same date):
//! `fnptr`, `fnptr_copied`, `fnptr_param` and `foreign_twin` built exit 0 with no
//! diagnostic at all — and `p(u32::MAX)` through `fnptr`'s library, linked into a
//! verify-off `main`, RETURNED 0, where the verify-off build panics (the witness,
//! `foreign_requires_callee_as_value_really_overflows.rs`). `map_last` and
//! `once_last_o3` were refused only by an unrelated row (the whole-function
//! panic-freedom row, `runtime_checked`; resp. the O3 `Const::Closure` gap), with
//! no `requires` note.
//! `fnptr_default` was refused by the indirect-call gate with no note naming
//! `add1` (the note named local items only). `local_twin` and `direct` kept their
//! verdicts (exit 0; refused by the direct call's `[precond] FAILED` row).
//!
//! AFTER: memory-safe asks the same gate (`uncharged_callable`), with the note
//! naming a `requires`-carrying item — local or foreign, or inside a std closure
//! the MIR inliner built — and the fix. The rule is parity with the other
//! fail-closed lanes, not only `requires`-carrying targets: a pointer from a
//! parameter (`fnptr_param`) may be one minted where no gate looks, and a foreign
//! target with no `requires` (`foreign_twin`) is code with no verdict here whose
//! DIRECT call memory-safe already refuses (its absent-callee row), so both are
//! refused too, without the `requires` note (`forbid-output`). That is the
//! capability cost, and each such shape is refused on every other fail-closed lane.
//! A local `requires`-free item reified and called (`local_twin`) still compiles.
//!
//! THE CLASSIFIER SKIP (review of the change above, 2026-09-30). One safe
//! `let _q = &raw const s.a;` makes the classifier skip the body
//! (`TreatedAsAssumption(AddressOfField)`), and memory-safe demoted that skip to one
//! assumption row without asking what the body calls — before the gate above is
//! reached, and although a skipped body charges none of its calls. BEFORE (a stage 1
//! of `3c29e31164` and of `fbc6068e3`, measured 2026-09-30): `skip_fnptr`,
//! `skip_direct`, `skip_let` and `skip_map` built exit 0 with only the
//! `Trust: ASSUMPTION [addr-of-field]` line, and `p(u32::MAX)` through
//! `skip_fnptr`'s and `skip_direct`'s libraries RETURNED 0; the same bodies without
//! the borrow are refused (`fnptr`, `direct`, `map_last`), as is the skip itself on
//! strict, the default policy and certify. AFTER: the demotion is withheld for a
//! body that calls a `requires`-carrying function directly (`skip_direct`,
//! `skip_let`) or that the gate refuses (`skip_fnptr`, `skip_map`), so the skip is
//! refused as on the other lanes, its policy note saying why.
//!
//! Merged onto main (integ/stage1-batch4), whose own rule for the same skip
//! (`memory_safe_assumption_uncharged_edges`, 631b03f8ea) withholds the demotion for
//! ANY call out of the verified closure, a fn-pointer call included. Both rules are
//! asked and the note carries each reason that fires, so the four refusals above
//! keep their notes. `skip_twin` (a `requires`-free local item reified and called
//! in a skipped body) was admitted by the L2 rule alone; main's edge rule refuses
//! it ("a call through a function pointer"), so it is now check-fail. Not run on
//! this branch.

extern crate requires_callee_dep as dep;

#[cfg(fnptr)]
pub fn p(y: u32) -> u32 {
    //[fnptr]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`: a function called through a fn pointer
    //[fnptr]~| NOTE add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = dep::add1;
    fp(y)
}

#[cfg(fnptr_copied)]
pub fn p(y: u32) -> u32 {
    //[fnptr_copied]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`: a function called through a fn pointer
    //[fnptr_copied]~| NOTE add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = dep::add1;
    let g = fp;
    g(y)
}

#[cfg(map_last)]
pub fn p(v: &[u32; 3]) -> Option<u32> {
    //[map_last]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`: a function called through a fn pointer
    //[map_last]~| NOTE add1` carries a `requires` its callers owe
    v.iter().copied().map(dep::add1).last()
}

#[cfg(fnptr_param)]
pub fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    //[fnptr_param]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::call`: a function called through a fn pointer
    f(y)
}

#[cfg(foreign_twin)]
pub fn p(y: u32) -> u32 {
    //[foreign_twin]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`: a function called through a fn pointer
    let fp: fn(u32) -> u32 = dep::add1_wrapping;
    fp(y)
}

#[cfg(local_twin)]
pub fn half(x: u32) -> u32 {
    x / 2
}
#[cfg(local_twin)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[local_twin]~vv ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`
//[local_twin]~v NOTE this function has no obligation of its own
pub fn p(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = half;
    fp(y)
}

#[cfg(direct)]
pub fn p(y: u32) -> u32 {
    //[direct]~^ ERROR Trust memory-safe verification failed for `reject_foreign_requires_callee_as_value::p`: at least one result is not an authenticated memory-safe assumption
    dep::add1(y)
}

#[cfg(fnptr_default)]
pub fn p(y: u32) -> u32 {
    //[fnptr_default]~^ ERROR Trust strict verification failed for `reject_foreign_requires_callee_as_value::p`
    //[fnptr_default]~| NOTE add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = dep::add1;
    fp(y)
}

#[cfg(any(skip_fnptr, skip_direct, skip_let, skip_map, skip_twin))]
pub struct S {
    pub a: u32,
}

#[cfg(skip_fnptr)]
pub fn p(y: u32, s: &S) -> u32 {
    //[skip_fnptr]~^ ERROR Trust full verification skipped `reject_foreign_requires_callee_as_value::p`
    //[skip_fnptr]~| NOTE (`@trust-indirect-callee`) — here `dep::add1`, which carries a `requires` its callers owe
    let _q = &raw const s.a;
    let fp: fn(u32) -> u32 = dep::add1;
    fp(y)
}

#[cfg(skip_direct)]
pub fn p(y: u32, s: &S) -> u32 {
    //[skip_direct]~^ ERROR Trust full verification skipped `reject_foreign_requires_callee_as_value::p`
    //[skip_direct]~| NOTE memory-safe did not admit this skip as an assumption: that assumption would stand for the body's own panic-freedom only, and a skipped body charges none of its calls, so it cannot stand for the call to `dep::add1`, which carries a `requires` its callers owe
    let _q = &raw const s.a;
    dep::add1(y)
}

#[cfg(skip_let)]
pub fn p(y: u32, s: &S) -> u32 {
    //[skip_let]~^ ERROR Trust full verification skipped `reject_foreign_requires_callee_as_value::p`
    //[skip_let]~| NOTE so it cannot stand for the call to `dep::add1`, which carries a `requires` its callers owe
    let _q = &raw const s.a;
    let g = dep::add1;
    g(y)
}

#[cfg(skip_map)]
pub fn p(v: &[u32; 3], s: &S) -> Option<u32> {
    //[skip_map]~^ ERROR Trust full verification skipped `reject_foreign_requires_callee_as_value::p`
    //[skip_map]~| NOTE (`@trust-indirect-callee`) — here `dep::add1`, which carries a `requires` its callers owe
    let _q = &raw const s.a;
    v.iter().copied().map(dep::add1).last()
}

#[cfg(skip_twin)]
pub fn half(x: u32) -> u32 {
    x / 2
}
#[cfg(skip_twin)]
pub fn p(y: u32, s: &S) -> u32 {
    //[skip_twin]~^ ERROR Trust full verification skipped `reject_foreign_requires_callee_as_value::p`
    //[skip_twin]~| NOTE a call through a function pointer
    let _q = &raw const s.a;
    let fp: fn(u32) -> u32 = half;
    fp(y)
}
