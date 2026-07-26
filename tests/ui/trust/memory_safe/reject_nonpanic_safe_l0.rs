//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
//
// Memory-safe is not a blanket "safe function may fail" switch. A forced
// over-budget allocation is an availability/design L0 failure, not a Rust
// bounds/overflow/division/assertion panic, so it must remain fatal even though
// the source contains no unsafe code.
pub fn oversized_allocation() -> Vec<u8> {
    //~^ ERROR Trust memory-safe verification failed for `reject_nonpanic_safe_l0::oversized_allocation`
    //~| WARN Trust Level 0 safety verification incomplete for `reject_nonpanic_safe_l0::oversized_allocation`
    Vec::with_capacity(1 << 28)
}
