//@ known-bug: rust-lang#112213
//@ compile-flags: -Copt-level=2
//@ run-pass
//
// Trust: KNOWN_BUG — Non-deterministic LLVM misoptimization on x86_64 where
// adding debug prints or other observable side effects changes the optimization
// outcome (Heisenbug pattern). Related to LLVM's pointer provenance model.
// Will be resolved by trust-cg backend (tRust #815-#832).
//
// Regression test: Documents the Heisenbug pattern where observation affects
// optimization results. The test itself may or may not trigger the bug depending
// on LLVM version and optimization decisions.

#[inline(never)]
fn compare_ptrs(a: usize, b: usize) -> bool {
    a == b
}

/// This function demonstrates the Heisenbug pattern:
/// the result of pointer comparison can change depending on
/// whether intermediate values are observed (printed, stored, etc.)
#[inline(never)]
fn heisen_compare() -> (bool, bool) {
    let a = {
        let v = 0u8;
        &v as *const _ as usize
    };
    let b = {
        let v = 0u8;
        &v as *const _ as usize
    };

    // Without observation, LLVM may optimize these differently
    let without_observe = a == b;
    let with_fn_call = compare_ptrs(a, b);

    (without_observe, with_fn_call)
}

fn main() {
    let (inline_result, fn_result) = heisen_compare();

    // Due to the Heisenbug, these may or may not be equal.
    // The inline comparison and function-call comparison can
    // produce different results because LLVM optimizes them
    // differently based on provenance tracking.
    // We just document that the function executes without crashing.
    let _ = (inline_result, fn_result);
}
