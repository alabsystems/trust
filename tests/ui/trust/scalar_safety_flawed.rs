//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
//@ check-fail
//! Full verification rejects proven-unsafe code that rustc's OWN lints do not
//! catch. The operands are runtime values (so `unconditional_panic` cannot fire):
//! `div`'s divisor can be 0 and `shl`'s shift amount can be >= the bit width.
//! The SMT verifier refutes both (div-by-zero / shift-overflow counterexamples);
//! under strict batteries-on verification each is a build ERROR, not a warning.

pub fn div(x: i32, y: i32) -> i32 {
    x / y
}

pub fn shl(x: u32, n: u32) -> u32 {
    x << n
}

fn main() {
    let _ = div(10, 2);
    let _ = shl(1, 3);
}
