//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
//
// A function containing `unsafe` is never eligible
// for a memory-safe assumption: this unchecked out-of-bounds read is possible UB
// and must remain a hard error in every verifier policy.
pub fn oob(s: &[u8], i: usize) -> u8 {
    //~^ ERROR Trust Level 0 safety verification incomplete for `reject_unsafe_ub::oob`
    //~| ERROR Trust strict verification failed for `reject_unsafe_ub::oob`
    // SAFETY: (intentionally unjustified — `i` is not proven `< s.len()`)
    unsafe { *s.get_unchecked(i) }
}
