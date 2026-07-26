//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
//
// A known panic-capable safe call whose body cannot be lowered is an explicit,
// authenticated memory-safe assumption. It remains visible and unproved, but
// the raw compiler must agree with Targo that this narrow row may conditionally
// compile.
pub fn unwrap_opt(o: Option<u32>) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `demote_explicit_lowering_gap::unwrap_opt`
    o.unwrap()
}
