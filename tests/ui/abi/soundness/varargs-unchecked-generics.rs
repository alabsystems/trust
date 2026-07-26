// tRust regression test for rust-lang/rust#61275
//
// SOUNDNESS BUG: Variadic (C-style "...") arguments are completely unchecked
// when passed through generic parameters. The Rust compiler does not verify
// that the types of variadic arguments match what the callee expects, because
// the variadic portion of a C function signature carries no type information.
//
// In C, this is "merely" undefined behavior that programmers must avoid. But
// Rust's type system should prevent passing incorrect types to variadic
// functions — especially since Rust already requires `unsafe` for calling
// variadic extern functions. The problem is that generic wrappers can forward
// arguments to variadic functions without any type checking on the variadic
// portion.
//
// Impact: Passing an f32 where a C function expects double (the default
// promotion for float in C varargs) corrupts the value. Passing a u8 where
// a C function expects int similarly corrupts. These are silent data
// corruption bugs that are invisible to the type checker.
//
// Status: open upstream since 2019, no fix. tRust should enforce type
// checking on variadic arguments.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/61275

//@ check-pass

// Demonstrate the type system hole: we can pass any type as a variadic arg
// through generics without the compiler checking ABI compatibility.

extern "C" {
    // printf expects: format string, then variadic args following C promotion
    // rules (float promotes to double, char/short promote to int, etc.)
    fn printf(fmt: *const i8, ...) -> i32;
}

// This wrapper is generic over T and passes it as a variadic argument.
// The compiler does NOT check that T is appropriate for C varargs.
// For example, passing an f32 is wrong (C promotes float to double in varargs),
// and passing a bool or u8 is wrong (C promotes to int).
unsafe fn print_value<T>(fmt: *const i8, val: T) -> i32 {
    // BUG: The compiler does not check that `T` is valid as a C variadic
    // argument. If T is f32, this will be passed as 4 bytes but the callee
    // (printf with %f) expects 8 bytes (double). This reads 4 bytes of
    // garbage from the stack.
    printf(fmt, val)
}

fn main() {
    // This compiles and runs, but if we passed an f32 where printf expects
    // a double (via %f), we'd get corrupted output. The type system should
    // catch this but doesn't when going through generics.
    //
    // Safe demonstration: pass an i32 which is valid for %d.
    let fmt = b"%d\n\0".as_ptr() as *const i8;
    unsafe {
        // This is fine: i32 matches %d
        print_value(fmt, 42i32);

        // This would be UB but compiles: f32 does NOT match %f (needs f64/double)
        // Uncomment to observe corruption:
        // let float_fmt = b"%f\n\0".as_ptr() as *const i8;
        // print_value(float_fmt, 3.14f32);  // BUG: f32 not promoted to f64
    }
}
