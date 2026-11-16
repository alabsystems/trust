//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `x % 2` over `&i32` reaches core's `<i32 as Rem>::rem`, which checks the zero
//! divisor, then the `MIN % -1` overflow in a second block, then computes the
//! remainder: the exact member lane pairs no Assert with its operation and refused
//! the member, which failed the whole function (ordsweep2 collections/c04). Like the
//! other foundational-member Assert refusals it is now the policy-B advisory (std
//! keeps its own runtime check); certify still refuses it.
pub fn keep_even(mut v: Vec<i32>) -> Vec<i32> {
    v.retain(|x| x % 2 == 0);
    v
}
