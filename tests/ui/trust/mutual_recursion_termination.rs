//@ revisions: ab three_cycle even_odd_unmeasured even_odd_measured not_decreasing
//@ revisions: one_member_measured three_measured wrong_position self_count self_unbounded
//@ revisions: trait_methods_measured closure_cycle
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[even_odd_measured] build-pass
//@[three_measured] build-pass
//@[self_count] build-pass
//@[trait_methods_measured] build-pass
//@[closure_cycle] check-fail
//@[ab] check-fail
//@[three_cycle] check-fail
//@[even_odd_unmeasured] check-fail
//@[not_decreasing] check-fail
//@[one_member_measured] check-fail
//@[wrong_position] check-fail
//@[self_unbounded] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! MUTUAL RECURSION IS CHARGED TERMINATION (docs/KNOWN_HAZARDS.md, "CLOSED
//! 2026-09-25 — mutual recursion verified and could abort on stack overflow").
//!
//! Before: a self-recursive fn minted a `[termination]` row, but a call into
//! ANOTHER member of the caller's recursion SCC minted none, so `a`/`b` below
//! built exit 0 and aborted with a stack overflow (134) at run time.
//!
//! The ruling (owner-delegated): calls within a recursion SCC get the same
//! termination obligation self recursion gets, and terminating mutual recursion
//! is admitted exactly when a measure proves it. The measure rule: every member
//! carries a function-level `decreases` naming one integer parameter, and at
//! every call into the SCC (self calls included) the CALLEE's measure at the
//! call's arguments must be strictly below the caller's at entry and the
//! caller's must be non-negative. The rows are the self-call rows with the
//! callee's measure substituted; SCC membership and each callee's measure are
//! computed by the compiler from resolved `DefId`s.
//!
//! Revisions:
//! * `ab`, `three_cycle` — infinite mutual recursion, no measure: refused, one
//!   unprovable `[termination]` row per call into the cycle.
//! * `even_odd_unmeasured` — TERMINATING mutual recursion with no measure:
//!   refused. This is the documented over-refusal, the same bar `count` meets:
//!   add `decreases` to every member (see `even_odd_measured`).
//! * `even_odd_measured`, `three_measured` — measured mutual recursion verifies;
//!   `three_measured` puts the measure at a different parameter position in each
//!   member, so each call reads the CALLEE's measure at the callee's position.
//! * `not_decreasing` — measured, but one call passes the measure unchanged.
//! * `one_member_measured` — one member has no measure: not comparable, refused.
//! * `wrong_position` — the call descends the callee's NON-measure argument.
//! * `self_count`, `self_unbounded` — direct self recursion, unchanged.
//! * `trait_methods_measured` — the cycle runs through two trait impls' methods;
//!   the calls resolve (by `DefId`) to the local impls, so the rule applies.
//! * `closure_cycle` — recursion through a closure. A closure cannot carry a
//!   `decreases` clause, so the cycle is refused: the disclosed over-refusal.

#[cfg(ab)]
pub fn a(n: u64) -> u64 { //[ab]~ ERROR Trust strict verification failed for
    //[ab]~^ NOTE [termination] UNKNOWN
    //[ab]~| NOTE is in a recursion cycle through `b`
    b(n)
}
#[cfg(ab)]
pub fn b(n: u64) -> u64 { //[ab]~ ERROR Trust strict verification failed for
    //[ab]~^ NOTE [termination] UNKNOWN
    //[ab]~| NOTE is in a recursion cycle through `a`
    a(n)
}

#[cfg(three_cycle)]
pub fn a(n: u64) -> u64 { //[three_cycle]~ ERROR Trust strict verification failed for
    //[three_cycle]~^ NOTE [termination] UNKNOWN
    b(n)
}
#[cfg(three_cycle)]
pub fn b(n: u64) -> u64 { //[three_cycle]~ ERROR Trust strict verification failed for
    //[three_cycle]~^ NOTE [termination] UNKNOWN
    c(n)
}
#[cfg(three_cycle)]
pub fn c(n: u64) -> u64 { //[three_cycle]~ ERROR Trust strict verification failed for
    //[three_cycle]~^ NOTE [termination] UNKNOWN
    a(n)
}

#[cfg(even_odd_unmeasured)]
pub fn even(n: u32) -> bool { //[even_odd_unmeasured]~ ERROR Trust strict verification failed for
    //[even_odd_unmeasured]~^ NOTE [termination] UNKNOWN
    //[even_odd_unmeasured]~| NOTE mutual recursion is admitted only on a measure
    if n == 0 { true } else { odd(n - 1) }
}
#[cfg(even_odd_unmeasured)]
pub fn odd(n: u32) -> bool { //[even_odd_unmeasured]~ ERROR Trust strict verification failed for
    //[even_odd_unmeasured]~^ NOTE [termination] UNKNOWN
    if n == 0 { false } else { even(n - 1) }
}

#[cfg(even_odd_measured)]
pub fn even(n: u32) -> bool //[even_odd_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases n
{
    if n == 0 { true } else { odd(n - 1) }
}
#[cfg(even_odd_measured)]
pub fn odd(n: u32) -> bool //[even_odd_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases n
{
    if n == 0 { false } else { even(n - 1) }
}

#[cfg(three_measured)]
pub fn a(n: u32) -> u32 //[three_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases n
{
    if n == 0 { 0 } else { b(n - 1) }
}
#[cfg(three_measured)]
pub fn b(m: u32) -> u32 //[three_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases m
{
    if m == 0 { 1 } else { c(7, m - 1) }
}
#[cfg(three_measured)]
pub fn c(k: u32, j: u32) -> u32 //[three_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases j
{
    if j == 0 { k } else { a(j - 1) }
}

#[cfg(not_decreasing)]
pub fn even(n: u32) -> bool //[not_decreasing]~ ERROR Trust strict verification failed for
    //[not_decreasing]~^ NOTE [termination] UNKNOWN
    decreases n
{
    if n == 0 { true } else { odd(n) }
}
#[cfg(not_decreasing)]
pub fn odd(n: u32) -> bool //[not_decreasing]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
    decreases n
{
    if n == 0 { false } else { even(n - 1) }
}

#[cfg(one_member_measured)]
pub fn even(n: u32) -> bool //[one_member_measured]~ ERROR Trust Level 0 safety verification incomplete for
    //[one_member_measured]~^ ERROR Trust strict verification failed for
    //[one_member_measured]~| NOTE is in a recursion cycle through `odd`
    decreases n
{
    if n == 0 { true } else { odd(n - 1) }
}
#[cfg(one_member_measured)]
pub fn odd(n: u32) -> bool { //[one_member_measured]~ ERROR Trust strict verification failed for
    //[one_member_measured]~^ NOTE [termination] UNKNOWN
    if n == 0 { false } else { even(n - 1) }
}

#[cfg(wrong_position)]
pub fn a(n: u32) -> u32 //[wrong_position]~ ERROR Trust strict verification failed for
    //[wrong_position]~^ NOTE [termination] UNKNOWN
    decreases n
{
    if n == 0 { 0 } else { c(n - 1, n) }
}
#[cfg(wrong_position)]
pub fn c(k: u32, j: u32) -> u32 //[wrong_position]~ ERROR Trust strict verification failed for
    //[wrong_position]~^ NOTE [termination] UNKNOWN
    decreases j
{
    if k == 0 { 2 } else { a(j) }
}

#[cfg(self_count)]
pub fn count(n: u32) -> u32 //[self_count]~ NOTE Trust verification: 3 proved, 0 failed, 0 unknown
    decreases n
{
    if n == 0 { 0 } else { count(n - 1) }
}

#[cfg(self_unbounded)]
pub fn r(n: u64) -> u64 { //[self_unbounded]~ ERROR Trust Level 0 safety verification incomplete for
    //[self_unbounded]~^ ERROR Trust strict verification failed for
    //[self_unbounded]~| NOTE [termination] UNKNOWN
    r(n + 1)
}

#[cfg(trait_methods_measured)]
pub trait Step {
    fn step(&self, n: u32) -> u32;
}
#[cfg(trait_methods_measured)]
pub struct P;
#[cfg(trait_methods_measured)]
pub struct Q;
#[cfg(trait_methods_measured)]
impl Step for P {
    fn step(&self, n: u32) -> u32 //[trait_methods_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
        decreases n
    {
        if n == 0 { 0 } else { Q.step(n - 1) }
    }
}
#[cfg(trait_methods_measured)]
impl Step for Q {
    fn step(&self, n: u32) -> u32 //[trait_methods_measured]~ NOTE Trust verification: 2 proved, 0 failed, 0 unknown
        decreases n
    {
        if n == 0 { 1 } else { P.step(n - 1) }
    }
}

#[cfg(closure_cycle)]
pub fn depth(v: &[u32]) -> u32 { //[closure_cycle]~ ERROR Trust strict verification failed for
    //[closure_cycle]~^ NOTE [termination] UNKNOWN
    //[closure_cycle]~| NOTE is in a recursion cycle through `depth::{closure#0}`
    if v.is_empty() {
        0
    } else {
        let f = |s: &[u32]| depth(s); //[closure_cycle]~ ERROR Trust strict verification failed for
        //[closure_cycle]~^ NOTE [termination] UNKNOWN
        f(&v[1..])
    }
}
