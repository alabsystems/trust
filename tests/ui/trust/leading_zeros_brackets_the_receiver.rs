//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! For an unsigned receiver, `leading_zeros() >= k` exactly when the receiver is
//! below `2^(bits-k)`. Without that bracket the count was only `[0, bits]`, and the
//! next-power-of-two shape below (sweep `r01g`) was refuted with `lz = 0` for a
//! receiver of 1. The twin `_refused.rs` keeps the off-by-one and the signed
//! receiver refused.
pub fn round_up_pow2(x: u32) -> u32 {
    if x <= 1 {
        return 1;
    }
    if x > (1 << 31) {
        return 0;
    }
    1u32 << (32 - (x - 1).leading_zeros())
}

pub fn bit_length(x: u64) -> u32 {
    if x == 0 {
        return 0;
    }
    let t = [0u8; 64];
    let _ = t[(63 - x.leading_zeros()) as usize];
    64 - x.leading_zeros()
}
