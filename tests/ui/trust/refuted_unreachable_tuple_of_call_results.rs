//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify -Cpanic=abort
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! Class `v-refuted-unreachable` (2026-09-27 inventory), the RE-READ half: a `match`
//! over a TUPLE built from two call results. rustc lowers it into a cascade of switches
//! that re-read the same field's discriminant into fresh temps, the last one covering
//! only `Some` with `otherwise -> Unreachable`:
//!
//! ```text
//! bb2: _3 = (move _4, move _5); _7 = discriminant(_3.0); switch _7 [0: bb4, 1: bb3, _: bb5]
//! bb3: _9 = discriminant(_3.1); switch _9 [0: bb8, 1: bb6, _: bb5]
//! bb6: _8 = discriminant(_3.0); switch _8 [1: bb7, _: bb5]
//! bb5: unreachable
//! ```
//!
//! Every read lies after the calls, where the verifier used to tie none of them, so the
//! solver read `_3.0` as `_7 = 1` in bb2 and `_8 = 0` in bb6. Before (trust main
//! `8c39674bbb`, stage 1, default policy): `[unreach] FAILED (ay-in-process);
//! counterexample: .. _7 = 1, _8 = 0, _9 = 1 ..`, a build error on correct Rust. The
//! tuple is never borrowed and no `Drop` names it, so the re-reads are tied
//! (`generate::build_discriminant_cse_facts`, arm (b) since `dd7ec4e5af`; arm (c) licenses
//! them too) and the row is solver-UNSAT. That left each path's contradiction holding only
//! modulo the tie, which the clean kernel cannot use, so on trust main `5a5545798b` the row
//! was not kernel-certified (measured on the real-MIR twin, `pair` in
//! `crates/trust-vcgen/tests/discriminant_cse_owned_aggregate_realmir.rs`). The path-guard
//! splice now renders the subset switch through the read it is tied to, and `trust-certify`
//! closes the path `_7 = 1 ∧ ¬(_7 = 1)` as a unit, so the row is kernel-certified under the
//! default policy and under `certify`.
//!
//! `get` is a same-crate helper, so the caller carries no absent-callee row: the
//! `Unreachable` block is `pair`'s only obligation.

#[inline(never)]
pub fn get(x: u32) -> Option<u32> {
    if x > 3 { Some(x) } else { None }
}

pub fn pair(a: u32, b: u32) -> u32 {
    //~^ NOTE Trust verification: 1 proved, 0 failed
    //~| NOTE of which 1 kernel-certified
    match (get(a), get(b)) {
        (None, None) => 0,
        (None, _) => 1,
        (_, None) => 2,
        (Some(x), Some(y)) => x ^ y,
    }
}
