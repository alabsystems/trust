//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Discriminant re-reads of an OWNED, never-exposed aggregate stay tied after a
//! CALL (TRUST-10).
//!
//! `cmp_slices` is bit-vec 0.9.1's `impl Ord for BitVec` (`src/lib.rs:1991`) on
//! two slice iterators. rustc builds `_5 = (a.next(), b.next())` and reads
//! `discriminant(_5.1)` into three temps across the arms, one shared
//! `otherwise -> unreachable` behind them. It was reported
//!
//!     [unreach] FAILED (ay-in-process); counterexample: _10 = 0, _11 = 0, _12 = 1, _13 = 1, …
//!
//! — two reads of the one unwritten field disagreeing, which no execution does
//! (replayed against `<[bool]>::cmp` on every pair of slices up to length 5).
//! The CSE facts that tie such reads were withheld from every block after a
//! `Call`, a barrier that exists for a SHARED-REF pointee a call can mutate; no
//! call can reach an aggregate whose address is never taken.
//!
//! THE STRICT BUILD IS THE ASSERTION: the one obligation must prove, so a
//! refuted `[unreach]` row fails this file. The exposed-aggregate controls, which
//! safe source cannot produce, are hand-built MIR in trust-vcgen's `src/tests.rs`
//! (`exposed_owned_aggregate_field_discriminants_are_not_tied_after_a_call`).
use std::cmp::Ordering;

pub fn cmp_slices(a: &[bool], b: &[bool]) -> Ordering {
    let mut a = a.iter();
    let mut b = b.iter();
    loop {
        match (a.next(), b.next()) {
            (Some(x), Some(y)) => match x.cmp(y) {
                Ordering::Equal => {}
                otherwise => return otherwise,
            },
            (None, None) => return Ordering::Equal,
            (None, _) => return Ordering::Less,
            (_, None) => return Ordering::Greater,
        }
    }
}
