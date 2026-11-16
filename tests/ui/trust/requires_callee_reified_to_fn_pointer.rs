//@ revisions: fnptr fnptr_strict fnptr_certify as_cast_certify method_certify extern_c_certify
//@ revisions: copied_certify generic_item_certify overflow_certify
//@ revisions: reqfree_certify ensures_only_certify direct_proved_certify direct_unproved
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[fnptr_strict] compile-flags: -Ztrust-policy=strict
//@[fnptr_certify] compile-flags: -Ztrust-policy=certify
//@[as_cast_certify] compile-flags: -Ztrust-policy=certify
//@[method_certify] compile-flags: -Ztrust-policy=certify
//@[extern_c_certify] compile-flags: -Ztrust-policy=certify
//@[copied_certify] compile-flags: -Ztrust-policy=certify
//@[generic_item_certify] compile-flags: -Ztrust-policy=certify
//@[overflow_certify] compile-flags: -Ztrust-policy=certify
//@[reqfree_certify] compile-flags: -Ztrust-policy=certify
//@[ensures_only_certify] compile-flags: -Ztrust-policy=certify
//@[direct_proved_certify] compile-flags: -Ztrust-policy=certify
//@[fnptr] check-fail
//@[fnptr_strict] check-fail
//@[fnptr_certify] check-fail
//@[as_cast_certify] check-fail
//@[method_certify] check-fail
//@[extern_c_certify] check-fail
//@[copied_certify] check-fail
//@[generic_item_certify] check-fail
//@[overflow_certify] check-fail
//@[reqfree_certify] check-fail
//@[ensures_only_certify] check-fail
//@[direct_proved_certify] check-pass
//@[direct_unproved] check-fail
//@ dont-check-compiler-stderr
//@[fnptr] dont-require-annotations: ERROR
//@[fnptr_strict] dont-require-annotations: ERROR
//@[fnptr_certify] dont-require-annotations: ERROR
//@[as_cast_certify] dont-require-annotations: ERROR
//@[method_certify] dont-require-annotations: ERROR
//@[extern_c_certify] dont-require-annotations: ERROR
//@[copied_certify] dont-require-annotations: ERROR
//@[generic_item_certify] dont-require-annotations: ERROR
//@[overflow_certify] dont-require-annotations: ERROR
//@[direct_proved_certify] dont-require-annotations: ERROR
//@[direct_unproved] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A LOCAL function with a `requires`, reified to a fn pointer and called through
//! it, must be charged its precondition or refused — never called for free.
//!
//! The function is verified UNDER its `requires` (an entry hypothesis; each DIRECT
//! caller is charged a `Precondition` row). The indirect-call gate's
//! reified-constant carve-out (`indirect_callee_is_a_reified_constant`) resolved
//! the pointer to the local item and accepted the call because the item "is
//! verified as its own root" — true of its body only under the clause nothing
//! at this call charged.
//!
//! BEFORE (stage 1 of origin/main `8b8d68d1abe`, m3's std, measured 2026-09-29):
//! every check-fail revision below built exit 0 — `certify` included, with no
//! diagnostic; `p`'s only row a `native-verification-gap` (`unknown`) — and a
//! verify-off `main` calling `p(0)` divided by zero (exit 101; `extern_c`
//! aborted, 134). `overflow` is worse than a panic: `add1(x) requires x < 100
//! { x + 1 }` reached through the pointer with `u32::MAX` RETURNED 0 from the
//! certify-built library — its overflow check was gone, the row having been
//! proved under the `requires` — while the verify-off build of the same library
//! panics. So the default lane's "keeps its runtime check" reading did not hold
//! either, and the refusal is on every fail-closed lane.
//!
//! AFTER: the carve-out requires the reified item to owe no caller precondition
//! (`local_fn_item_is_verified_unconditionally`), so the call falls to the
//! indirect-call gate: `Trust strict verification failed` with a note naming the
//! function and the fix (call it directly, e.g. from a closure, where the
//! precondition is charged).
//!
//! Controls, unchanged: a `requires`-free pointer (`reqfree`), an `ensures`-only
//! pointer (`ensures_only` — its body is proved for every input and nothing at an
//! indirect call assumes the postcondition), a guarded DIRECT call
//! (`direct_proved`) all pass `certify`; an unguarded direct call
//! (`direct_unproved`) is refused by its own `Precondition` row, as before.
//! Companions: `requires_callee_handed_to_generic_code.rs` (the item as a value
//! handed to std) and `trait_impl_requires_charged_to_no_caller.rs`.

#[cfg(not(any(overflow_certify, method_certify, extern_c_certify, generic_item_certify)))]
pub fn div10(x: u32) -> u32 requires x != 0 {
    100 / x
}

#[cfg(any(fnptr, fnptr_strict, fnptr_certify))]
pub fn p(y: u32) -> u32 {
    //[fnptr,fnptr_strict,fnptr_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[fnptr,fnptr_strict,fnptr_certify]~| NOTE `div10` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = div10;
    fp(y)
}

#[cfg(as_cast_certify)]
pub fn p(y: u32) -> u32 {
    //[as_cast_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[as_cast_certify]~| NOTE `div10` carries a `requires` its callers owe
    (div10 as fn(u32) -> u32)(y)
}

#[cfg(method_certify)]
pub struct S;
#[cfg(method_certify)]
impl S {
    pub fn div(&self, x: u32) -> u32 requires x != 0 {
        100 / x
    }
}
#[cfg(method_certify)]
pub fn p(y: u32) -> u32 {
    //[method_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[method_certify]~| NOTE `S::div` carries a `requires` its callers owe
    let fp: fn(&S, u32) -> u32 = S::div;
    fp(&S, y)
}

#[cfg(extern_c_certify)]
pub extern "C" fn div10c(x: u32) -> u32 requires x != 0 {
    100 / x
}
#[cfg(extern_c_certify)]
pub fn p(y: u32) -> u32 {
    //[extern_c_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[extern_c_certify]~| NOTE `div10c` carries a `requires` its callers owe
    let fp: extern "C" fn(u32) -> u32 = div10c;
    fp(y)
}

#[cfg(copied_certify)]
pub fn p(y: u32) -> u32 {
    //[copied_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[copied_certify]~| NOTE `div10` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = div10;
    let g = fp;
    g(y)
}

#[cfg(generic_item_certify)]
pub fn div10g<T: Copy>(x: u32, _t: T) -> u32 requires x != 0 {
    100 / x
}
#[cfg(generic_item_certify)]
pub fn p(y: u32) -> u32 {
    //[generic_item_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[generic_item_certify]~| NOTE `div10g` carries a `requires` its callers owe
    let fp: fn(u32, u8) -> u32 = div10g::<u8>;
    fp(y, 0)
}

#[cfg(overflow_certify)]
pub fn add1(x: u32) -> u32 requires x < 100 {
    x + 1
}
#[cfg(overflow_certify)]
pub fn p(y: u32) -> u32 {
    //[overflow_certify]~^ ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
    //[overflow_certify]~| NOTE `add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = add1;
    fp(y)
}

#[cfg(reqfree_certify)]
pub fn half(x: u32) -> u32 {
    x / 2
}
#[cfg(reqfree_certify)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[reqfree_certify]~vv ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
//[reqfree_certify]~v NOTE this function has no obligation of its own
pub fn p(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = half;
    fp(y)
}

#[cfg(ensures_only_certify)]
pub fn half(x: u32) -> u32 ensures result <= x {
    x / 2
}
#[cfg(ensures_only_certify)]
// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[ensures_only_certify]~vv ERROR Trust strict verification failed for `requires_callee_reified_to_fn_pointer::p`
//[ensures_only_certify]~v NOTE this function has no obligation of its own
pub fn p(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = half;
    fp(y)
}

#[cfg(direct_proved_certify)]
pub fn p(y: u32) -> u32 {
    if y != 0 { div10(y) } else { 0 }
}

#[cfg(direct_unproved)]
pub fn p(y: u32) -> u32 {
    //[direct_unproved]~^ ERROR Trust Level 0 safety verification incomplete for `requires_callee_reified_to_fn_pointer::p`
    div10(y)
}
