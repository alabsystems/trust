//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2 -Ztrust-verify-profile=unix_hardened -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict --crate-type=lib
#![no_std]

// A reference-valued slot is still outside the promotion lane. Discovering this
// else borrow must preserve Promote(init is borrow ptr), not materialize &&mut.
pub fn reference_valued_promotion(value: Option<u32>) -> u32 {
    //~^ ERROR Promote(init is borrow ptr)
    let mut outer = 11;
    let mut reference = &mut outer;
    let Some(_) = value else {
        let double = &mut reference;
        **double = 29;
        return outer;
    };
    outer
}
