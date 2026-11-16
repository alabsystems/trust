//@ revisions: strict memory_safe
//@ needs-trust-verify
//@ aux-build: memory_safe_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-fail
//! `Option::<dep::Boom>::unwrap_or_default` runs the verify-off dependency's
//! `Default::default` — `unreachable_unchecked()` — on the caller's behalf. The
//! bridge lowers such a closure-driving consumer as an `Assert(false)` may-panic
//! marker with a bridge-local per-site row that carries no assumption prefix, and
//! nothing minted the counted whole-function carrier for it, so the edge reached NO
//! public obligation. Measured on stage-1 436c9eb6d0, in BOTH lanes: the zero-row
//! bodies built rc=0 with no error or warning (JSON: one `native-verification-gap`
//! row, `unknown`), and `guarded_index_beside_dep_default` — one incidental guarded
//! index beside the same call — published `proved: 1, total: 1`.
//!
//! `two_defaults` is the folded twin: `Option::<u32>::unwrap_or_default` is a bundled
//! member, so the body DOES carry the whole-function panic-freedom aggregate, which
//! folds the dependency edge's marker too; strict tolerated that aggregate as a kept
//! runtime check (rc=0 on 436c9eb6d0) although one of its sites runs no check at all.
//!
//! Now the compiler charges a foreign-reaching consumer call that no counted row
//! carries (`uncharged_foreign_closure_consumer_edges`: a `native-verification-gap`
//! row in every lane, an error in strict), strict refuses to tolerate an unproved
//! aggregate that folds a masked source, and memory-safe admits a body with a masked
//! source only on an all-proved, fully charged row set.
extern crate memory_safe_unverified_dep as dep;

pub fn option_default_reaches_dep_ub(o: Option<dep::Boom>) -> u32 {
    //~^ ERROR Trust
    o.unwrap_or_default().0
}

pub fn result_default_reaches_dep_ub(r: Result<dep::Boom, u8>) -> u32 {
    //~^ ERROR Trust
    r.unwrap_or_default().0
}

pub fn guarded_index_beside_dep_default(o: Option<dep::Boom>, v: &[u32], i: usize) -> u32 {
    //~^ ERROR Trust
    if i < v.len() { o.unwrap_or_default().0 ^ v[i] } else { 0 }
}

pub fn two_defaults(o: Option<dep::Boom>, p: Option<u32>) -> u32 {
    //~^ ERROR Trust
    o.unwrap_or_default().0 ^ p.unwrap_or_default()
}

/// The dependency type inside a TUPLE: the walk reads the consumer's type arguments
/// through their own generic arguments. rc=0 in both lanes on stage-1 436c9eb6d0.
pub fn tuple_default_reaches_dep_ub(o: Option<(dep::Boom, u32)>) -> u32 {
    //~^ ERROR Trust
    o.unwrap_or_default().1
}

/// The same consumer behind a `take()`. rc=0 in both lanes on stage-1 436c9eb6d0.
pub fn take_then_default_reaches_dep_ub(o: &mut Option<dep::Boom>) -> u32 {
    //~^ ERROR Trust
    o.take().unwrap_or_default().0
}
