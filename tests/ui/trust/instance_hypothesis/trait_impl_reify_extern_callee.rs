//~ NOTE "proved":1,"failed":0,"unknown":1,"timed_out":0,"skipped":0,"runtime_checked":0,"cached":0,"total":2}
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
//@[strict] check-fail
//@[certify] check-fail
//! OD-1 phase 1 review (2026-10-04, D1): a concrete instance of a TRAIT-IMPL method
//! that carries an instance hypothesis gets its discharge row. The mention
//! `<W<[u8; 3]> as Run>::run` names the trait item `Run::run`; the hypothesis sits on
//! the impl's method, so the carrier test must run on the RESOLVED instance. Before
//! the fix the mention was dropped unresolved: no discharge row, and the strict lane
//! exited 0 although the instance indexes `[u8; 3]` at 5. Now the instance's site
//! resolves to `<[u8; 3] as Index<usize>>::index`, a callee outside this crate that
//! this compilation has no verdict for: the discharge row is `unknown` (line 1: the
//! `no_obligations` row and the discharge row), an error on every fail-closed lane.
//! The inherent twin (`V::<[u8; 3]>::inh`) already behaved this way.
use std::ops::Index;

pub trait Run {
    fn run(&self) -> u8;
}

pub struct W<S>(pub S);

impl<S: Index<usize, Output = u8>> Run for W<S> {
    fn run(&self) -> u8 {
        //[certify]~^ ERROR Trust certify verification failed
        self.0[5]
    }
}

// ZERO-ROW-GATE (2026-10-10): zero bridged obligations plus a call no authenticated registry discharges publish an `unknown` row; refused.
//[certify,strict]~vv ERROR Trust strict verification failed for `trait_impl_reify_extern_callee::reify_trait_method`
//[certify,strict]~v NOTE this function has no obligation of its own
pub fn reify_trait_method() -> fn(&W<[u8; 3]>) -> u8 {
    //[advisory]~^ WARN Trust instance discharge not established for `trait_impl_reify_extern_callee::reify_trait_method`: 1 instance(s)
    //[strict]~^^ ERROR Trust instance discharge not established for `trait_impl_reify_extern_callee::reify_trait_method`: 1 instance(s)
    //[certify]~^^^ ERROR Trust instance discharge not established for `trait_impl_reify_extern_callee::reify_trait_method`: 1 instance(s)
    <W<[u8; 3]> as Run>::run
}
