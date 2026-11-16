//@ revisions: ref_item_any ref_ref_item_any refmut_item_any ref_trait_default_any
//@ revisions: dyn_ref_item_any overflow_ref_any ref_item_map_last generic_trait_ref_any
//@ revisions: fnptr_param_ref_any dyn_param_any refmut_dyn_param_any generic_param_ref_any
//@ revisions: dyn_supertrait_param_any impl_param_ref_any box_fnptr_param_any
//@ revisions: reqfree_ref_any reqfree_ref_ref_any ensures_only_ref_any ref_closure_any
//@ revisions: refmut_closure_any concrete_trait_item_ref_any generic_len local_ctor_ref_map
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[ref_item_any] compile-flags: -Ztrust-policy=certify
//@[ref_ref_item_any] compile-flags: -Ztrust-policy=certify
//@[refmut_item_any] compile-flags: -Ztrust-policy=certify
//@[ref_trait_default_any] compile-flags: -Ztrust-policy=certify
//@[dyn_ref_item_any] compile-flags: -Ztrust-policy=certify
//@[overflow_ref_any] compile-flags: -Ztrust-policy=certify
//@[fnptr_param_ref_any] compile-flags: -Ztrust-policy=certify
//@[dyn_param_any] compile-flags: -Ztrust-policy=certify
//@[refmut_dyn_param_any] compile-flags: -Ztrust-policy=certify
//@[generic_param_ref_any] compile-flags: -Ztrust-policy=certify
//@[dyn_supertrait_param_any] compile-flags: -Ztrust-policy=certify
//@[impl_param_ref_any] compile-flags: -Ztrust-policy=certify
//@[reqfree_ref_any] compile-flags: -Ztrust-policy=certify
//@[reqfree_ref_ref_any] compile-flags: -Ztrust-policy=certify
//@[ensures_only_ref_any] compile-flags: -Ztrust-policy=certify
//@[ref_closure_any] compile-flags: -Ztrust-policy=certify
//@[refmut_closure_any] compile-flags: -Ztrust-policy=certify
//@[concrete_trait_item_ref_any] compile-flags: -Ztrust-policy=certify
//@[generic_len] compile-flags: -Ztrust-policy=certify
//@[ref_item_any] check-fail
//@[ref_ref_item_any] check-fail
//@[refmut_item_any] check-fail
//@[ref_trait_default_any] check-fail
//@[dyn_ref_item_any] check-fail
//@[overflow_ref_any] check-fail
//@[ref_item_map_last] check-fail
//@[generic_trait_ref_any] check-fail
//@[fnptr_param_ref_any] check-fail
//@[dyn_param_any] check-fail
//@[refmut_dyn_param_any] check-fail
//@[generic_param_ref_any] check-fail
//@[dyn_supertrait_param_any] check-fail
//@[impl_param_ref_any] check-fail
//@[box_fnptr_param_any] check-fail
//@[reqfree_ref_any] check-pass
//@[reqfree_ref_ref_any] check-pass
//@[ensures_only_ref_any] check-fail
//@[ref_closure_any] check-pass
//@[refmut_closure_any] check-pass
//@[concrete_trait_item_ref_any] check-fail
//@[generic_len] check-pass
//@[local_ctor_ref_map] check-pass
//@ dont-check-compiler-stderr
//@[ref_item_any] dont-require-annotations: ERROR
//@[ref_ref_item_any] dont-require-annotations: ERROR
//@[refmut_item_any] dont-require-annotations: ERROR
//@[ref_trait_default_any] dont-require-annotations: ERROR
//@[dyn_ref_item_any] dont-require-annotations: ERROR
//@[overflow_ref_any] dont-require-annotations: ERROR
//@[ref_item_map_last] dont-require-annotations: ERROR
//@[generic_trait_ref_any] dont-require-annotations: ERROR
//@[fnptr_param_ref_any] dont-require-annotations: ERROR
//@[dyn_param_any] dont-require-annotations: ERROR
//@[refmut_dyn_param_any] dont-require-annotations: ERROR
//@[generic_param_ref_any] dont-require-annotations: ERROR
//@[dyn_supertrait_param_any] dont-require-annotations: ERROR
//@[impl_param_ref_any] dont-require-annotations: ERROR
//@[box_fnptr_param_any] dont-require-annotations: ERROR
//@[generic_len] dont-require-annotations: ERROR
//@[local_ctor_ref_map] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A callable handed to std THROUGH A REFERENCE (`any(&pos)`, `any(&&pos)`,
//! `any(&mut f)`, `any(f)` with `f: &dyn Fn`) or a `Box` is called by core's
//! forwarding impls (`impl<F: Fn> Fn for &F`, `&mut F`, `Box<F>`), so it must
//! be asked exactly as the same callable handed by value is.
//!
//! `callable_type_arg_is_unresolved` asked only the TOP-LEVEL type argument:
//! `F = &fn(&u32) -> bool {pos}` fell to `_ => false` and counted as resolved.
//!
//! BEFORE (stage 1 of the requires-gate change `141b0488896`, m3's std,
//! adversarial review 2026-09-29, then again on stage 1 of origin/main
//! `cb8406c0bf0` for this test): every certify revision below built exit 0 under
//! `-Ztrust-policy=certify` and a verify-off `main` on `[0, 1, 2]` divided by
//! zero (exit 101). `overflow_ref_any` RETURNED `true` for `u32::MAX` — the
//! verify-on `big` had no overflow check left — where the verify-off build of
//! the same library panics. `ref_item_map_last`, `generic_trait_ref_any` and
//! `box_fnptr_param_any` built exit 0 on the default policy (certify refused
//! them) and panicked. The `*_param_*` revisions are the caller-supplied
//! callable of `scripts/fn_pointer_witness.sh`, independent of any `requires`:
//! a verify-off `main` passing a dividing function panicked through each.
//!
//! AFTER: `peel_fn_forwarding_layers` strips `&`, `&mut` and `Box` first; an
//! `Fn`-family `dyn`, a type parameter or alias that may be called, and a
//! requires-carrying local item are unresolved: `Trust strict verification
//! failed`, with the requires note where a local item carries the clause.
//!
//! Controls keep their verdicts (certify unless noted): a requires-free item
//! and an `ensures`-only item by reference, a local closure by `&` and by
//! `&mut`, a concrete trait impl item by reference, a generic `[T]::len` (an
//! unbounded `T` is not callable), and a local constructor by reference to
//! `map` on the default policy (certify refuses core's `Map`, unchanged).
//! Companions: `requires_callee_handed_to_generic_code.rs`,
//! `local_item_naming_no_verified_body_as_value.rs`.

#[cfg(any(
    ref_item_any,
    ref_ref_item_any,
    refmut_item_any,
    dyn_ref_item_any
))]
pub fn pos(x: &u32) -> bool requires *x != 0 {
    100 / *x > 1
}

#[cfg(ref_item_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[ref_item_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[ref_item_any]~| NOTE `pos` carries a `requires` its callers owe
    v.iter().any(&pos)
}

#[cfg(ref_ref_item_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[ref_ref_item_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[ref_ref_item_any]~| NOTE `pos` carries a `requires` its callers owe
    v.iter().any(&&pos)
}

#[cfg(refmut_item_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[refmut_item_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[refmut_item_any]~| NOTE `pos` carries a `requires` its callers owe
    let mut f = pos;
    v.iter().any(&mut f)
}

#[cfg(dyn_ref_item_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[dyn_ref_item_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(&pos as &dyn Fn(&u32) -> bool)
}

#[cfg(any(ref_trait_default_any, generic_trait_ref_any))]
pub trait Tr {
    fn pos(x: &u32) -> bool requires *x != 0 {
        100 / *x > 1
    }
}
#[cfg(any(ref_trait_default_any, generic_trait_ref_any))]
pub struct S;
#[cfg(any(ref_trait_default_any, generic_trait_ref_any))]
impl Tr for S {}

#[cfg(ref_trait_default_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[ref_trait_default_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[ref_trait_default_any]~| NOTE `Tr::pos` carries a `requires` its callers owe
    v.iter().any(&<S as Tr>::pos)
}

#[cfg(generic_trait_ref_any)]
fn g<T: Tr>(v: &[u32; 3]) -> bool {
    //[generic_trait_ref_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::g`
    //[generic_trait_ref_any]~| NOTE `Tr::pos` carries a `requires` its callers owe
    v.iter().any(&T::pos)
}
#[cfg(generic_trait_ref_any)]
pub fn p(v: &[u32; 3]) -> bool {
    g::<S>(v)
}

#[cfg(overflow_ref_any)]
pub fn big(x: &u32) -> bool requires *x < 100 {
    *x + 1 == 0
}
#[cfg(overflow_ref_any)]
pub fn p(v: &[u32; 3]) -> bool {
    //[overflow_ref_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[overflow_ref_any]~| NOTE `big` carries a `requires` its callers owe
    v.iter().any(&big)
}

#[cfg(ref_item_map_last)]
pub fn div10(x: u32) -> u32 requires x != 0 {
    100 / x
}
#[cfg(ref_item_map_last)]
pub fn p(v: &[u32; 3]) -> usize {
    //[ref_item_map_last]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    //[ref_item_map_last]~| NOTE `div10` carries a `requires` its callers owe
    match v.iter().copied().map(&div10).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(fnptr_param_ref_any)]
pub fn p(v: &[u32; 3], f: fn(&u32) -> bool) -> bool {
    //[fnptr_param_ref_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(&f)
}

#[cfg(dyn_param_any)]
pub fn p(v: &[u32; 3], f: &dyn Fn(&u32) -> bool) -> bool {
    //[dyn_param_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(f)
}

#[cfg(refmut_dyn_param_any)]
pub fn p(v: &[u32; 3], f: &mut dyn FnMut(&u32) -> bool) -> bool {
    //[refmut_dyn_param_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(f)
}

#[cfg(generic_param_ref_any)]
pub fn p<F: Fn(&u32) -> bool>(v: &[u32; 3], f: &F) -> bool {
    //[generic_param_ref_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(f)
}

#[cfg(dyn_supertrait_param_any)]
pub trait Pred: Fn(&u32) -> bool {}
#[cfg(dyn_supertrait_param_any)]
impl<T: Fn(&u32) -> bool> Pred for T {}
#[cfg(dyn_supertrait_param_any)]
pub fn p(v: &[u32; 3], f: &dyn Pred) -> bool {
    //[dyn_supertrait_param_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(f)
}

#[cfg(impl_param_ref_any)]
pub struct W<F>(pub F);
#[cfg(impl_param_ref_any)]
impl<F: Fn(&u32) -> bool> W<F> {
    pub fn p(&self, v: &[u32; 3]) -> bool {
        //[impl_param_ref_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::W::<F>::p`
        v.iter().any(&self.0)
    }
}

#[cfg(box_fnptr_param_any)]
pub fn p(v: &[u32; 3], f: Box<fn(&u32) -> bool>) -> bool {
    //[box_fnptr_param_any]~^ ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
    v.iter().any(f)
}

// ---- controls ----

#[cfg(any(reqfree_ref_any, reqfree_ref_ref_any))]
pub fn pos(x: &u32) -> bool {
    *x > 1
}
#[cfg(reqfree_ref_any)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(&pos)
}
#[cfg(reqfree_ref_ref_any)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(&&pos)
}

#[cfg(ensures_only_ref_any)]
pub fn pos(x: &u32) -> bool ensures result == (*x > 1) {
    *x > 1
}
#[cfg(ensures_only_ref_any)]
// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[ensures_only_ref_any]~vv ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
//[ensures_only_ref_any]~v ERROR Trust Level 0 safety verification incomplete for `callable_handed_to_std_through_a_reference::p`
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(&pos)
}

#[cfg(ref_closure_any)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(&|x: &u32| *x > 1)
}

#[cfg(refmut_closure_any)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn p(v: &[u32; 3]) -> bool {
    let mut c = |x: &u32| *x > 1;
    v.iter().any(&mut c)
}

#[cfg(concrete_trait_item_ref_any)]
pub trait Tp {
    fn pos(x: &u32) -> bool;
}
#[cfg(concrete_trait_item_ref_any)]
pub struct S;
#[cfg(concrete_trait_item_ref_any)]
impl Tp for S {
    fn pos(x: &u32) -> bool {
        *x > 1
    }
}
#[cfg(concrete_trait_item_ref_any)]
// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[concrete_trait_item_ref_any]~vv ERROR Trust strict verification failed for `callable_handed_to_std_through_a_reference::p`
//[concrete_trait_item_ref_any]~v ERROR Trust Level 0 safety verification incomplete for `callable_handed_to_std_through_a_reference::p`
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(&<S as Tp>::pos)
}

#[cfg(generic_len)]
pub fn p<T>(v: &[T]) -> usize {
    v.len()
}

#[cfg(local_ctor_ref_map)]
pub struct Wr(pub u32);
#[cfg(local_ctor_ref_map)]
pub fn p(v: &[u32; 3]) -> usize {
    v.iter().copied().map(&Wr).count()
}
