//~ NOTE "proved":0,"failed":0,"unknown":3,"timed_out":0,"skipped":3,"runtime_checked":0,"cached":0,"total":3}
//~| NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":1,"runtime_checked":0,"cached":0,"total":2}
//@ revisions: advisory strict certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//@[strict] check-pass
//@[certify] check-fail
//! OD-1 open shapes (2026-10-04; docs/DECISION_QUEUE.md "OD-1" item 14): a call through
//! a closure type parameter, `<F as Fn<(u32,)>>::call` with `F: Fn(u32) -> u32` taken
//! by reference, is an open generic dispatch on the body's own parameter and is
//! ADMITTED by the same predicate as `<T as Tr>::m` (no trait list). Before this change
//! its row was the hypothesis alone, yet strict REFUSED the body as "an unresolved
//! indirect call": the indirect-call gate read the dispatched `Self` (`F`) as an
//! unresolved callable type argument, so the rows and the gate disagreed. The gate now
//! exempts the dispatched `Self` of an ADMITTED site only (every other type argument is
//! still asked). Line 1, first pin: `apply` publishes its hypothesis, the inventory row
//! and the global-alloc row, all skipped; second pin: `use_apply` names
//! `apply::<{closure}>`, whose discharge row is `proved` (counted skipped, no credit)
//! beside its whole-function row. Strict passes CONDITIONALLY; certify refuses.
pub fn apply<F: Fn(u32) -> u32>(f: &F, x: u32) -> u32 {
    //[certify]~^ ERROR Trust certify verification failed for `fn_bound_admitted_site_passes_strict::apply`: 1 instance hypothesis row(s)
    f(x)
}

pub fn use_apply() -> u32 {
    apply(&|x: u32| x / 2, 7)
}
