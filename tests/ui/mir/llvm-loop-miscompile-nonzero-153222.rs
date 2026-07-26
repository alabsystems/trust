// Regression test for rust-lang/rust#153222 / llvm/llvm-project#183906.
//
// LLVM's IndVarSimplify::predicateLoopExits() miscompiles loops containing
// infinite inner loops by failing to account for divergence effects from
// normal control flow. This causes it to incorrectly predicate loop exits,
// leading to NonZero<i8> containing zero at runtime in safe Rust.
//
// The bug manifests only at optimization levels where IndVarSimplify runs.
//
// Trust: Workaround applied in rustc_codegen_llvm/src/llvm_util.rs by
// disabling --indvars-predicate-loops.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>

//@ revisions: opt0 opt1 opt2 opt3
//@[opt0] compile-flags: -C opt-level=0
//@[opt1] compile-flags: -C opt-level=1
//@[opt2] compile-flags: -C opt-level=2
//@[opt3] compile-flags: -C opt-level=3
//@ run-pass

use std::num::NonZero;

#[inline(never)]
pub fn func() -> NonZero<i8> {
    let mut i = -5;
    let mut j = -4;
    loop {
        let x = loop {
            if let Some(v) = NonZero::new(j) {
                break v;
            }
            j += 1;
        };
        i += 1;
        j += 1;
        if i == 0 {
            return x;
        }
    }
}

fn main() {
    let result = func();
    // The bug caused result to be NonZero(0), which violates the NonZero
    // invariant. The correct result is NonZero(1) (j=1 when i reaches 0).
    assert_ne!(result.get(), 0, "NonZero<i8> must never be zero (rust-lang/rust#153222)");
    assert_eq!(result.get(), 1, "func() should return NonZero(1)");
}
