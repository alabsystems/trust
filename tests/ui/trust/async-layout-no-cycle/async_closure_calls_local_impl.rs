//@ revisions: off adv strict
//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[strict] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[off] check-pass
//@[adv] check-pass
//@[strict] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//! An async closure whose body calls a LOCAL trait impl, derived or hand-written.
//!
//! Drop-in (release gate): stock rustc accepts this crate, and so does every
//! revision here. On `origin/main` `93f05556da` the verified lanes rejected it
//! with E0391: `check_crate` demands the async closure's by-move body
//! (`coroutine_by_move_body_def_id`), which builds the coroutine's MIR
//! (`mir_built`); the trust-ir producer's MIR oracle, inside that `mir_built`,
//! renamed the devirtualized `Default::default` call only when
//! `is_mir_available(<R as Default>::default)` — and `is_mir_available` of a local
//! def reads `mir_keys`, which demands the by-move body of every async closure,
//! this one included. The oracle now asks `TyCtxt::trust_local_def_has_mir`, which
//! answers `mir_keys` membership from HIR, the resolver's Clean registry and the
//! def kind, and the analysis seam checks it against `mir_keys` in every verified
//! compilation. `strict` refuses the async closures on Trust verdicts (an
//! unmodeled coroutine-closure state machine, the executor-protocol premise), which
//! drop-in permits, and on nothing else. Since r15 (2026-10-07) the async closures'
//! synthetic by-move bodies (`{synthetic#0}`) are in the coverage universe and are
//! verified in a check build too, so strict refuses them on the same premise.

#[derive(Default)]
pub struct Derived;

pub struct Hand;
impl Default for Hand {
    fn default() -> Hand {
        Hand
    }
}

pub fn derived() {
    let _x = async |_a: u32| -> Derived { Default::default() };
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `async_closure_calls_local_impl::derived::{closure#0}`: 1 obligation(s) were not proved
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::derived::{closure#0}`: 1 obligation(s) were not fully verified
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::derived::{closure#0}::{closure#0}`: coroutine executor-protocol premise is unproved
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::derived::{closure#0}::{synthetic#0}`: coroutine executor-protocol premise is unproved
}

pub fn hand() {
    let _x = async |_a: u32| -> Hand { Default::default() };
    //[strict]~^ ERROR Trust Level 0 safety verification incomplete for `async_closure_calls_local_impl::hand::{closure#0}`: 1 obligation(s) were not proved
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::hand::{closure#0}`: 1 obligation(s) were not fully verified
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::hand::{closure#0}::{closure#0}`: coroutine executor-protocol premise is unproved
    //[strict]~| ERROR Trust strict verification failed for `async_closure_calls_local_impl::hand::{closure#0}::{synthetic#0}`: coroutine executor-protocol premise is unproved
}
