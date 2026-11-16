//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! E9-CONSTANT-UINT-MIXED-1, the wrong-value twin of
//! `e9_constant_uint_mixed_carrier_discharge.rs`: the mixed-carrier mint of
//! `fn six(flag: bool) -> u8 { 6 }` must not be identified with an island `7`.

clean {
    def seven_isl (flag : Bool) : UInt8 := 7
}

pub fn six(flag: bool) -> u8
    //~^ ERROR Trust Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed
    ensures result == seven_isl(flag)
    //~^ ERROR `seven_isl` was not discharged by definitional equality: the two sides are not
{
    6
}

fn main() {}
