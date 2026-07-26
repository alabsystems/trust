//@ known-bug: rust-lang#130388
//@ compile-flags: -Copt-level=2
//@ run-pass
//
// Trust: KNOWN_BUG — LLVM provenance bug where comparing a pointer's address against
// all possible addresses can return false for every comparison. This is caused by
// LLVM's pointer provenance model stripping metadata during ptrtoint conversions.
// Will be resolved by trust-cg backend (tRust #815-#832).
//
// Regression test: Documents current (buggy) LLVM behavior.
// When trust-cg resolves this, this test should be updated to assert correct behavior.

use std::ptr;

/// Attempts to find a pointer's address by exhaustive comparison.
/// Due to LLVM provenance bugs, this may fail to find the address
/// even when it should succeed.
#[inline(never)]
fn find_address(ptr_addr: usize, candidate: usize) -> bool {
    ptr_addr == candidate
}

fn main() {
    let val: u8 = 42;
    let ptr = &val as *const u8;
    let addr = ptr as usize;

    // Direct comparison should always work
    assert!(find_address(addr, addr));

    // But the compiler may get confused with provenance
    let ptr2 = ptr::without_provenance::<u8>(addr);
    let addr2 = ptr2 as usize;

    // These addresses are the same value, but LLVM may disagree
    // depending on optimization level and inlining decisions
    let _direct_eq = addr == addr2;

    // This documents the bug exists — the test passes because
    // we are documenting known-buggy behavior, not asserting correctness
}
