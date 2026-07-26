// count_to — reconstructed generating source for
// fixtures/real-spec-corpus/count_to.json (commit 98f116b930).
//
// The guard-aware UPPER-bound synthesis flagship: SMT alone FAILS the
// postcondition ret <= n; the synthesized loop invariant 0 <= i AND i <= n
// (upper conjunct PROPOSED from the guard i < n, kernel-VERIFIED via
// counter_le_bound_preservation_proof) closes it through
// loop_postcondition_witness. Fully faithful, modulo exactly 3 axioms.
//
// Dump with:
//   trustc --crate-type lib -Ztrust-dump=mir-only:<dir> \
//     -Ztrust-policy=advisory count_to.rs
//
// NOTE ON RECONSTRUCTION: the original count_to.rs was a scratch file that was
// never checked in. The function text below (lines 23-31) and the two contract
// attribute lines are exactly pinned by the spans + MIR embedded in the
// checked-in count_to.json; this header preamble (lines 1-22) is NOT pinned by
// the dump (no span reaches it) and is authored for this reconstruction. The
// re-dump byte-comparison against count_to.json is what validates the fn text.
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![feature(contracts)]
#![allow(internal_features, incomplete_features, unused)]
#[core::contracts::requires(n >= 0)]
#[core::contracts::ensures(move |ret: &i32| *ret <= n)]
pub fn count_to(n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        i = i + 1;
    }
    i
}
