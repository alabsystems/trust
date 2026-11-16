//@ revisions: map_last map_count filter_last map_fold any_item any_item_certify self_map
//@ revisions: overflow_map_last
//@ revisions: reqfree_map_last ensures_only_map_last reqfree_any_certify guarded_closure
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[any_item_certify] compile-flags: -Ztrust-policy=certify
//@[reqfree_any_certify] compile-flags: -Ztrust-policy=certify
//@[map_last] check-fail
//@[map_count] check-fail
//@[filter_last] check-fail
//@[map_fold] check-fail
//@[any_item] check-fail
//@[any_item_certify] check-fail
//@[self_map] check-fail
//@[overflow_map_last] check-fail
//@[reqfree_map_last] check-pass
//@[ensures_only_map_last] check-pass
//@[reqfree_any_certify] check-pass
//@[guarded_closure] check-pass
//@ dont-check-compiler-stderr
//@[map_last] dont-require-annotations: ERROR
//@[map_count] dont-require-annotations: ERROR
//@[filter_last] dont-require-annotations: ERROR
//@[map_fold] dont-require-annotations: ERROR
//@[any_item] dont-require-annotations: ERROR
//@[any_item_certify] dont-require-annotations: ERROR
//@[self_map] dont-require-annotations: ERROR
//@[overflow_map_last] dont-require-annotations: ERROR
//@[reqfree_map_last] dont-require-annotations: ERROR
//@[ensures_only_map_last] dont-require-annotations: ERROR
//@[guarded_closure] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A LOCAL function with a `requires`, handed to generic code as a function
//! ITEM (`map(div10)`, `filter(pred)`, `any(pos)`), is called inside that code,
//! where no row of this crate charges its precondition. It must be refused.
//!
//! `callable_type_arg_is_unresolved` answered "resolved" for every local item
//! handed to a direct call ("verified as its own root"). For a `requires`-carrying
//! item that verification holds only under the clause, which the call inside
//! core's `Map::next`/`Filter::next`/`any` never establishes.
//!
//! BEFORE (stage 1 of origin/main `8b8d68d1abe`, m3's std, measured 2026-09-29):
//! every check-fail revision built exit 0 on the default policy (and on
//! `-Ztrust-policy=strict`), and a verify-off `main` on `[0, 1, 2]` divided by
//! zero (exit 101). `any_item_certify`
//! built exit 0 even under `certify`. `self_map` is the function handing ITSELF
//! to `map` (the termination charge alone made it conditional, not refused).
//! `overflow_map_last` is why "runtime-checked" was false: `add1(x) requires
//! x < 100 { x + 1 }` mapped over `[0, 1, u32::MAX]` RETURNED 0 — the
//! verify-on library had no overflow check left in `add1` — where the verify-off
//! build of the same library panics.
//!
//! AFTER: a local item that owes a caller precondition is an unresolved callable
//! (`local_fn_item_is_verified_unconditionally`): `Trust strict verification
//! failed`, with a note naming the item and the fix. The recommended fix is the
//! `guarded_closure` control: `map(|x| if x != 0 { div10(x) } else { 0 })` — the
//! closure's DIRECT call is charged and proved, and it passes the default policy
//! exactly as the `requires`-free `reqfree_map_last` does (both are refused by
//! `certify` for core's own `Map`, unchanged). `ensures_only_map_last` and
//! `reqfree_any_certify` keep their verdicts.
//! Companion: `requires_callee_reified_to_fn_pointer.rs`.

#[cfg(any(map_last, map_count, map_fold, guarded_closure))]
pub fn div10(x: u32) -> u32 requires x != 0 {
    100 / x
}

#[cfg(map_last)]
pub fn p(v: &[u32; 3]) -> usize {
    //[map_last]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[map_last]~| NOTE `div10` carries a `requires` its callers owe
    match v.iter().copied().map(div10).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(map_count)]
pub fn p(v: &[u32; 3]) -> usize {
    //[map_count]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[map_count]~| NOTE `div10` carries a `requires` its callers owe
    v.iter().copied().map(div10).count()
}

#[cfg(filter_last)]
pub fn pred(x: &u32) -> bool requires *x != 0 {
    100 / *x > 1
}
#[cfg(filter_last)]
pub fn p(v: &[u32; 3]) -> usize {
    //[filter_last]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[filter_last]~| NOTE `pred` carries a `requires` its callers owe
    match v.iter().copied().filter(pred).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(map_fold)]
pub fn p(v: &[u32; 3]) -> u32 {
    //[map_fold]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[map_fold]~| NOTE `div10` carries a `requires` its callers owe
    v.iter().copied().map(div10).fold(0u32, |a, b| a.wrapping_add(b))
}

#[cfg(any(any_item, any_item_certify))]
pub fn pos(x: &u32) -> bool requires *x != 0 {
    100 / *x > 1
}
#[cfg(any(any_item, any_item_certify))]
pub fn p(v: &[u32; 3]) -> bool {
    //[any_item,any_item_certify]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[any_item,any_item_certify]~| NOTE `pos` carries a `requires` its callers owe
    v.iter().any(pos)
}

#[cfg(self_map)]
pub fn f(n: u32) -> u32 requires n != 0 {
    //[self_map]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::f`
    //[self_map]~| NOTE `f` carries a `requires` its callers owe
    if n > 1 {
        match [n / 10].iter().copied().map(f).last() {
            Some(r) => r,
            None => 1,
        }
    } else {
        100 / n
    }
}

#[cfg(overflow_map_last)]
pub fn add1(x: u32) -> u32 requires x < 100 {
    x + 1
}
#[cfg(overflow_map_last)]
pub fn p(v: &[u32; 3]) -> u32 {
    //[overflow_map_last]~^ ERROR Trust strict verification failed for `requires_callee_handed_to_generic_code::p`
    //[overflow_map_last]~| NOTE `add1` carries a `requires` its callers owe
    match v.iter().copied().map(add1).last() {
        Some(r) => r,
        None => 7,
    }
}

#[cfg(reqfree_map_last)]
pub fn half(x: u32) -> u32 {
    x / 2
}
#[cfg(reqfree_map_last)]
pub fn p(v: &[u32; 3]) -> usize {
    match v.iter().copied().map(half).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(ensures_only_map_last)]
pub fn half(x: u32) -> u32 ensures result <= x {
    x / 2
}
#[cfg(ensures_only_map_last)]
pub fn p(v: &[u32; 3]) -> usize {
    match v.iter().copied().map(half).last() {
        Some(_) => 1,
        None => 0,
    }
}

#[cfg(reqfree_any_certify)]
pub fn pos(x: &u32) -> bool {
    *x > 1
}
#[cfg(reqfree_any_certify)]
// ZERO-ROW-GATE (2026-10-10) refused this zero-row body. Since 2026-10-15 (DECISION_QUEUE
// D103, VERIFIED-CALLABLE-ZERO-ROW-PARITY) the gate reads the drive-only consumer lane's
// decision for the call, which discharges it through the callable's own verdict: it builds.
pub fn p(v: &[u32; 3]) -> bool {
    v.iter().any(pos)
}

#[cfg(guarded_closure)]
pub fn p(v: &[u32; 3]) -> usize {
    match v.iter().copied().map(|x| if x != 0 { div10(x) } else { 0 }).last() {
        Some(_) => 1,
        None => 0,
    }
}
