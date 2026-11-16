//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off --crate-type=lib
// Divergence D4's root-fix (full-population frontier, wave-full-0831): a
// CONTRACT-ATTRIBUTED body takes the elision posture — `param_opaque`,
// SYMBOLIC: never spliced (a module claiming to represent the program must
// not omit its checks), never sampled (the differential refuses symbolic
// before sampling). The built MIR such a body ships carries the INJECTED
// contract checks and this lowering does not, so the two are DIFFERENT
// PROGRAMS on any check-tripping input — the measured divergence fed
// `typed_lane(x: i32) requires x > 0` its i32::MIN probe: THIR returned
// the identity, the oracle trapped on the requires assert. Detection is at
// the ATTRIBUTE spelling: under -Ztrust-verify=off the trust_contracts
// query answers EMPTY (measured) while the attr expansion has already
// injected the check. Lowering the checks themselves is the honest future
// widening; eliding them silently was the bug.

#[trust::requires(x > 0)]
pub fn positive_only(x: i32) -> i32 {
    x
}

#[trust::ensures(move |r: &i32| *r >= 0)]
pub fn clamped(x: i32) -> i32 {
    if x < 0 { 0 } else { x }
}

// No contract: the ordinary lanes, non-symbolic.
pub fn plain(x: i32) -> i32 {
    x + 1
}
