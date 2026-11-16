//@ revisions: default certify
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Injected is not pinned (2026-09-28): a same-crate callee whose `ensures`
//! only BOUNDS its result — with or without a `requires` guard — does not make a
//! solver model over that result an execution, so the D5-A screen withholds the
//! refutation instead of reporting it `FAILED`.
//!
//! Before (MEASURED on the `p_falsefail` probe): `dead_else_s` below was
//! `[overflow:sub] FAILED` on stage 1 AND on the pack, counterexample `_4 =
//! true, _5 = 4, _6 = false, a = 5` — `r = 4 <= a = 5` satisfies `smax`'s
//! contract, but `smax(5, 3)` is 5 and the `3 - r` arm is dead. Its twin over a
//! `clean`-cited `rmax` (`dead_else`) was FAILED the same way on stage 1. The
//! census had counted every callee whose summary INJECTS a clause as pinning
//! its destination.
//!
//! After: the screen pins a destination only where an injected clause
//! DETERMINES it (`_0 == E`, no `requires`) at a call site the injector admits
//! (`trust_vcgen::generate::summary_pins_result`). `dead_else_s` and
//! `dead_else_u` are held `UNKNOWN`s naming the callee; the build is still an
//! error in both revisions (a held row keeps no runtime-check tolerance). The
//! genuine bug through a DETERMINING contract (`three_bad`: `2 - 3`) stays a
//! refutation.
//!
//! Mentioned is not depended on (2026-09-29, review of cb/track-b): the screen
//! first read the WHOLE query, so it also held rows that merely CARRY a bounded
//! call's own injected `pre → post` fact. MEASURED on the review's probe
//! (`let _r = smax(20, 3); a - 10`): the pack said `[overflow:sub] FAILED;
//! counterexample … a = 0`, the first Track B stage 1 said `UNKNOWN … query
//! depends on the unmodeled return of … smax`, although `a - 10` underflows at
//! `a = 0` whatever `smax` returns. A row is now held only when its refutation
//! can DEPEND on the result — the violation's operands, a value the query
//! names, or a branch on any path to the violation is computed from it
//! (`GenericRefutationScope::row_is_independent_of`). `unused_result` and
//! `indep_after` below are FAILED again; `ctrl_dep_reach` (reached only through
//! `r > 100`) and `data_dep` (`(r + 1) - 10`) stay held, like `dead_else_*`.
//!
//! Every ERROR is annotated in both revisions, so an unexpected error on
//! `smax`, `umax` or `three` fails the file. Unit and
//! real-MIR coverage: `crates/trust-vcgen/src/refutation_scope.rs` and
//! `crates/trust-vcgen/tests/call_dest_refutation_scope_realmir.rs`.

pub fn smax(a: u64, b: u64) -> u64
    requires b <= a
    ensures result <= a
{
    if a < b { b } else { a }
}

pub fn dead_else_s(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_bounding_contract_held::smax`
    if a > 3 {
        let r = smax(a, 3);
        if r == a { 0 } else { 3 - r }
    } else {
        0
    }
}

pub fn umax(a: u64, b: u64) -> u64
    ensures result >= a
{
    if a < b { b } else { a }
}

pub fn dead_else_u(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_bounding_contract_held::umax`
    if a > 3 {
        let r = umax(a, 3);
        if r == a { 0 } else { 3 - r }
    } else {
        0
    }
}

pub fn three() -> u64
    ensures result == 3
{
    3
}

pub fn three_bad(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //[default]~| NOTE [overflow:sub] FAILED
    let r = three();
    if a > 3 { 2 - r } else { 0 }
}

// A genuine bug the bounded result can neither feed nor gate stays FAILED.
pub fn unused_result(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //[default]~| NOTE [overflow:sub] FAILED
    let _r = smax(20, 3);
    a - 10
}

pub fn indep_after(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //[default]~| NOTE [overflow:sub] FAILED
    let r = smax(20, 3);
    let x = a - 10;
    if r > 0 { x } else { 0 }
}

// Reached only when `r > 100`, i.e. only when `a > 100`: never underflows, and
// the model `a = 0, r = 101` is not a run. Held.
pub fn ctrl_dep_reach(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_bounding_contract_held::umax`
    let r = umax(a, 3);
    if r > 100 { a - 10 } else { 0 }
}

// `smax(20, 3)` is 20, so `(r + 1) - 10` never underflows; `r <= 20` lets the
// solver pick `r = 0`. Held.
pub fn data_dep(a: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `call_dest_bounding_contract_held::smax`
    let r = smax(20, 3);
    let w = r + 1;
    if a > 0 { w - 10 } else { 0 }
}
