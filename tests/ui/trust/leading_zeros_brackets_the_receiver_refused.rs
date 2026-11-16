//@ revisions: off_by_one signed sub_off_by_one
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Twin of `leading_zeros_brackets_the_receiver.rs`. `off_by_one`: `x` up to
//! `2^31` has `lz = 0` there, so the shift is by 32. `signed`: a negative `i32`
//! has `lz = 0` although it is below `2^31`, so the bracket must not apply.
//! `sub_off_by_one`: the receiver is the checked `x - 1` (stated as that
//! expression), and `x` up to `2^31 + 1` lets it reach `2^31`.
#[cfg(off_by_one)]
pub fn round_up(x: u32) -> u32 { //[off_by_one]~ ERROR verification
    if x == 0 {
        return 1;
    }
    if x > (1 << 31) {
        return 0;
    }
    1u32 << (32 - x.leading_zeros())
}

#[cfg(signed)]
pub fn shift_by_lz(x: i32) -> u32 { //[signed]~ ERROR verification
    1u32 << (32 - x.leading_zeros())
}

#[cfg(sub_off_by_one)]
pub fn round_up_wide(x: u32) -> u32 { //[sub_off_by_one]~ ERROR verification
    if x <= 1 {
        return 1;
    }
    if x > (1 << 31) + 1 {
        return 0;
    }
    1u32 << (32 - (x - 1).leading_zeros())
}
