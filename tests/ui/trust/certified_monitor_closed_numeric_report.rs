//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ rustc-env:TRUST_MONITOR_REPORT=1
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A variable-free verifier-language numeric term has mathematical-Int static
//! semantics. It must not borrow Clean's default Nat runtime carrier when the
//! two operations differ: Nat subtraction truncates at zero, while Int
//! subtraction does not. This is an explicit unmonitored frontier, never a
//! certified monitor for a different proposition.

pub fn closed_integer_subtraction()
    requires 0 - 1 == 0
    //~^ NOTE contract clause #0 (Requires) is unmonitored (variable-free integer subtraction has no exact Nat runtime monitor)
{
}
