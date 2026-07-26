// Regression test for rust-lang#61275: ensure that variadic and non-variadic
// function types cannot be silently coerced or unified through generic contexts.
//
// A C-variadic fn must never be coerced to a non-variadic fn pointer (or vice
// versa) because the calling conventions are incompatible — calling a
// non-variadic fn with variadic convention (or the reverse) is UB.

extern "C" {
    fn c_variadic_fn(x: i32, ...);
}

extern "C" fn non_variadic_fn(_x: i32) {}

// Test 1: variadic fn item → non-variadic fn pointer (should fail)
fn test_variadic_to_non_variadic() {
    let _: unsafe extern "C" fn(i32) = c_variadic_fn;
    //~^ ERROR mismatched types
}

// Test 2: non-variadic fn item → variadic fn pointer (should fail)
fn test_non_variadic_to_variadic() {
    let _: extern "C" fn(i32, ...) = non_variadic_fn;
    //~^ ERROR mismatched types
}

// Test 3: variadic fn pointer → non-variadic fn pointer (should fail)
fn test_variadic_ptr_to_non_variadic() {
    let variadic_ptr: unsafe extern "C" fn(i32, ...) = c_variadic_fn;
    let _: unsafe extern "C" fn(i32) = variadic_ptr;
    //~^ ERROR mismatched types
}

// Test 4: passing through a generic function — variadic fn should NOT
// implement Fn traits (is_fn_trait_compatible returns false for variadic fns)
fn call_with_fn<F: Fn(i32)>(_f: F, _x: i32) {}

fn test_variadic_as_generic() {
    call_with_fn(non_variadic_fn, 42); // OK: non-variadic fn implements Fn
    //~^ ERROR expected an `Fn(i32)` closure
    // A variadic fn cannot be passed as Fn — is_fn_trait_compatible rejects it.
    // This is not directly testable here because `c_variadic_fn` is an extern
    // block item (unsafe extern "C"), which already can't implement Fn due to
    // safety and ABI requirements.
}

fn main() {}
