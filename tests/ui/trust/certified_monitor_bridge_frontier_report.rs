//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ rustc-env:TRUST_MONITOR_REPORT=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `trust-spec-elab` can kernel-certify bitwise and literal-shift monitor trees,
//! but the compiler frontend/query has no exact structural nodes for those
//! operators and classifies them as unsupported before the static projector.
//! Native clauses must therefore remain explicitly unmonitored; source text
//! alone can never mint executable authority.

pub fn low_bit(x: u8) -> u8
    ensures result == (x & 1)
    //~^ NOTE contract clause #0 (Ensures) is unmonitored
{
    x & 1
}

pub fn shift_left(x: u8) -> u8
    ensures result == (x << 1)
    //~^ NOTE contract clause #0 (Ensures) is unmonitored
{
    x << 1
}
