//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
// R1 capability alarm for the effective-visibility case: `scaled` is reachable
// through an `#[inline] pub` caller, but is not downstream-nameable,
// symbol-exported, address-taken, a trait method, or generic. Its sole in-crate
// caller establishes `divisor = 4 != 0`. The `build-pass` expectation is met
// only because that closed-world fact arrives as sealed, kernel-replayed proof
// authority.
fn scaled(x: u32, divisor: u32) -> u32 {
    x / divisor
}
#[inline]
pub fn api(x: u32) -> u32 {
    scaled(x, 4)
}
