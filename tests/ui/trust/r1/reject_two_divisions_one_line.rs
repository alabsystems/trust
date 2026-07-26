//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
// MF-1 regression: two div-by-zero obligations on ONE source line (line 8). The in-crate
// caller establishes `divisor != 0` (so `x / divisor` is dischargeable) but `other = 0` is
// a real div-by-zero. R1 must prove only the first division and NOT spill that proof onto
// the second (the flip seam keys on kind+file+line+COL and refuses ambiguous keys), so the
// build still fails. If this ever build-passes, a violable VC was marked Proved.
fn f(x: u32, divisor: u32, y: u32, other: u32) -> u32 { //~ ERROR Level 0 safety verification incomplete
    //~| ERROR Trust strict verification failed for
    let _q = x / divisor; y / other
}
pub fn caller() -> u32 {
    f(10, 5, 99, 0)
}
