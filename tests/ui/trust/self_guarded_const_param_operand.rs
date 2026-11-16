//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! SELF-GUARDED-CONST-OPERAND-1 (2026-10-11): a checked operation over a CONSTANT
//! operand with a value identity — a const-generic `N`, or a keyed associated const
//! `T::U` — kept a vacuous statement-lane row beside its assert's own row.
//!
//! rustc does not fold these: `-N` extracts as `_1 = Eq(const N, const i32::MIN);
//! assert(!_1, OverflowNeg) -> bb1; bb1: _0 = Neg(const N)`. The statement row in
//! `bb1` sits under the assert's guard, so its violation is `NOT _1` beside `_1`'s
//! own definition: UNSAT by construction, `proved`, and kernel-certified at the
//! span of a check that fails for some instantiation. Every exact-binding
//! suppressor that removes that row for a PLACE operand refused a constant
//! (trust-vcgen `checked_vcs.rs`: `v2_operands_structurally_equal`,
//! `v2_eq_def_binds_compared_value`, `v2_build_assert_negation_vc`).
//!
//! Every function below panics for some instantiation (`neg_c::<{ i32::MIN }>()`,
//! `div_c::<0>(7)`, `shl_c::<32>(1)`, …), so no row of any of them may read proved.
//!
//! BEFORE (stage 1 of `5911b1325f`, `scratchpad/stage1-w23base`, each revision's
//! own flags plus `--cfg <revision> --emit=metadata`, measured 2026-10-11): both
//! revisions exit 1, and every function carries one `proved`, kernel-certified row
//! (`note: … of which 1 kernel-certified`, `summary: 0 trusted, 1 certified, …`;
//! `sdiv_c`/`srem_c` carry two). The negations have no FAILED row at all — the
//! assert lane left `RecognizedSafetyAssertProofGap(OverflowNeg)` — and the shifts
//! fail only a generic `[overflow]` row. So the `[negation] FAILED`,
//! `[shift:left] FAILED`, `[shift:right] FAILED`, `Trust verification: 0 proved,` and
//! `summary: 0 trusted, 0 certified,` annotations below are absent before the fix
//! (counted: zero occurrences of each in both revisions' output).
//!
//! AFTER (measured on the stage 1 of `999b006b87`, both revisions): each check carries exactly
//! one row, the assert lane's, and it is REFUTED; no function has a proved row.

pub trait Tr {
    const U: u32;
}

pub fn neg_c<const N: i32>() -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [negation] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    -N
}

pub fn neg_c8<const N: i8>() -> i8 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [negation] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    -N
}

// i128: a const param has no bitvector rendering, so both lanes take the Int
// constructors and the statement row is the same vacuity as below 128.
pub fn neg_c128<const N: i128>() -> i128 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [negation] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    -N
}

pub fn div_c<const N: u32>(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [divzero] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x / N
}

pub fn rem_c<const N: u32>(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [remzero] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x % N
}

pub fn sdiv_c<const N: i32>(x: i32) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [divzero] FAILED
    //~| NOTE [overflow:div] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x / N
}

pub fn srem_c<const N: i32>(x: i32) -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [remzero] FAILED
    //~| NOTE [overflow:rem] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x % N
}

// The const generic as the DIVIDEND: `N / -1` overflows at `N == i32::MIN`.
pub fn sdiv_c_dividend<const N: i32>() -> i32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [overflow:div] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    N / -1
}

pub fn shl_c<const N: u32>(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [shift:left] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x << N
}

pub fn shr_c<const N: u32>(x: u64) -> u64 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [shift:right] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x >> N
}

// A keyed associated const (`OpaqueOrigin::Const`): one value per key. The extra
// `unknown` row is the unmodeled-value refusal for the opaque operand, unchanged.
pub fn div_a<T: Tr>(x: u32) -> u32 {
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    //~| NOTE Trust verification: 0 proved,
    //~| NOTE [divzero] FAILED
    //~| NOTE summary: 0 trusted, 0 certified,
    x / T::U
}
