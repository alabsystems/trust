//@ revisions: bound bound_debuginfo result_eq_debuginfo
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[bound_debuginfo] compile-flags: -Cdebuginfo=2
//@[result_eq_debuginfo] compile-flags: -Cdebuginfo=2
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `let c = b; let b: u64 = ..;` leaves the MIR rows `b => _1`, `c => _1`,
//! `b => _3`. The debug-name collapse was last-write-wins per local, so the
//! parameter `_1` was named `c` and `b` survived on the shadow `_3` alone, where
//! the formula namespace read it as unique: the `ensures` clause's `b` bound the
//! narrow shadow and was PROVED and kernel-certified while the u128 parameter broke
//! it (`f(1 << 64, 10)`; review round 37, 2026-10-02). A source name whose rows
//! name two distinct locals now names neither, and the clause is not discharged.
#[cfg(any(bound, bound_debuginfo))]
pub fn f(b: u128, a: u64) -> u64 //[bound,bound_debuginfo]~ ERROR verification
    ensures b <= 18446744073709551615
{
    let c = b;
    let b: u64 = a / 2;
    if c == 7 {
        return 0;
    }
    b
}

#[cfg(result_eq_debuginfo)]
pub fn f(b: u128) -> u128 //[result_eq_debuginfo]~ ERROR verification
    ensures result == b
{
    let c = b;
    let b: u8 = (c % 256) as u8;
    b as u128
}
