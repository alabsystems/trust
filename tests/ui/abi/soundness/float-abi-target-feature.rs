// tRust regression test for rust-lang/rust#116344
//
// SOUNDNESS BUG: The ABI of f32/f64 types can be changed by -Ctarget-feature
// on i686 (32-bit x86). Disabling the `x87` feature or enabling `soft-float`
// changes how floating-point values are passed and returned. Functions compiled
// with different target features will disagree on calling convention.
//
// This is unsound because code calling methods from the standard library (which
// was compiled with default features) will use the wrong registers to pass or
// return float results. Setting -Ctarget-feature=-x87 or +soft-float introduces
// UB unless the standard library is rebuilt with the same flags.
//
// On x86_64, disabling SSE/SSE2 similarly affects float ABI (floats moved from
// XMM registers to the stack or x87 FPU stack).
//
// Status: upstream has a future-incompat warning (shipping in 1.84) with plans
// for a hard error. tRust should reject conflicting float ABI at compile time.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/116344

//@ check-pass

// Demonstrate the pattern: two functions with different implicit float ABIs.
// On i686 with -Ctarget-feature=-x87, this would change from x87 ST(0) returns
// to integer-register returns, breaking all callers compiled without the flag.

extern "C" fn return_float() -> f64 {
    3.14159
}

extern "C" fn accept_float(x: f64) -> f64 {
    x * 2.0
}

// If compiled with -Ctarget-feature=+soft-float (on a target that supports it),
// these functions would use integer registers for float values instead of
// FPU/SSE registers. Any caller compiled WITHOUT soft-float would read garbage
// from the wrong register.

#[inline(never)]
fn call_chain() -> f64 {
    // In a correct compiler, this chain works fine. But if different parts of
    // the program are compiled with different -Ctarget-feature flags affecting
    // float ABI, the return value of return_float() arrives in the wrong
    // register for accept_float().
    // Simulating cross-compilation-unit call where ABI might differ.
    // Using function pointers to prevent the compiler from inlining and
    // hiding the ABI mismatch.
    let f: extern "C" fn() -> f64 = return_float;
    let val = f();
    let g: extern "C" fn(f64) -> f64 = accept_float;
    g(val)
}

fn main() {
    let result = call_chain();
    // On a correctly compiled program, result should be ~6.28318
    // With ABI mismatch, result would be garbage.
    assert!(result > 6.0 && result < 7.0);
}
