//@ needs-trust-verify
//@ edition: 2021
//@ revisions: exact false_claim zero symbolic signed signed_trunc signed_euclid signed_false signed_overflow
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[exact] check-pass
//@[false_claim] check-fail
//@[zero] check-fail
//@[symbolic] check-fail
//@[signed] check-pass
//@[signed_trunc] check-pass
//@[signed_euclid] check-fail
//@[signed_false] check-fail
//@[signed_overflow] check-fail

// The original Clean CRC fixture remains the cross-language regression.
// These direct callers exercise the newly admitted source remainder itself.
#[cfg(exact)]
pub fn remainder(x: u32) -> u32
    ensures result == x % 2
{
    x % 2
}

#[cfg(false_claim)]
pub fn remainder(x: u32) -> u32 //[false_claim]~ ERROR Trust
    ensures result == (x % 2) + 1
{
    x % 2
}

#[cfg(zero)]
pub fn remainder(x: u32) -> u32 //[zero]~ ERROR Trust
    ensures result == x % 0
{
    x
}

#[cfg(symbolic)]
pub fn remainder(x: u32, divisor: u32) -> u32 //[symbolic]~ ERROR Trust
    requires divisor > 0
    ensures result == x % divisor
{
    x % divisor
}

// Signed remainder was a refusal control when this fixture landed. The
// verifier now admits it (DECISION_QUEUE, "Taken 2026-11-05 — the signed
// remainder control flips to accepted"), so these twins pin Rust's truncated
// semantics: -3 % 2 is -1, not the Euclidean 1, and MIN % -1 stays refused.
#[cfg(signed)]
pub fn remainder(x: i32) -> i32
    ensures result == x % 2
{
    x % 2
}

#[cfg(signed_trunc)]
pub fn remainder(x: i32) -> i32
    requires x == -3
    ensures result == -1
{
    x % 2
}

#[cfg(signed_euclid)]
pub fn remainder(x: i32) -> i32 //[signed_euclid]~ ERROR Trust
    requires x == -3
    ensures result == 1
{
    x % 2
}

#[cfg(signed_false)]
pub fn remainder(x: i32) -> i32 //[signed_false]~ ERROR Trust
    ensures result >= 0
{
    x % 2
}

#[cfg(signed_overflow)]
pub fn remainder(x: i32, divisor: i32) -> i32 //[signed_overflow]~ ERROR Trust
    requires divisor != 0
{
    x % divisor
}
