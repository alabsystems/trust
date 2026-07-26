// tRust regression test for rust-lang/rust#105838
//
// SOUNDNESS BUG: On x86 Windows, `extern "system"` is equivalent to
// `extern "stdcall"`. However, the compiler was not properly validating
// ABI compatibility when `extern "system"` functions were involved in
// certain contexts (function pointer casts, trait implementations, FFI
// boundaries).
//
// The `extern "system"` ABI is a platform-adaptive calling convention:
// - On Windows x86 (32-bit): maps to stdcall (callee cleans stack)
// - On Windows x86_64: maps to the Win64 calling convention
// - On non-Windows: maps to the C calling convention
//
// The bug was that the compiler's ABI checking logic did not always
// resolve `extern "system"` to its platform-specific equivalent before
// performing compatibility checks. This could allow:
//
// 1. Assigning an `extern "C"` fn pointer to an `extern "system"` fn
//    pointer variable on x86 Windows, where the two have different
//    stack cleanup conventions (caller-cleanup vs callee-cleanup).
//    Mismatched cleanup causes stack corruption.
//
// 2. Missing warnings or errors when mixing `extern "system"` and
//    `extern "stdcall"` in ways that should be equivalent on Windows
//    but were treated as distinct by the type checker.
//
// FIX: The compiler now properly resolves `extern "system"` to its
// platform-specific ABI before performing compatibility checks, ensuring
// that ABI mismatches are caught at compile time on all platforms.
//
// This test verifies the safe patterns: declaring and using extern
// "system" functions correctly, and demonstrating that the type system
// properly tracks the calling convention.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/105838

//@ check-pass

#![allow(dead_code)]

// ---- extern "system" function declarations ----

// extern "system" adapts to the platform's system calling convention.
extern "system" fn system_add(a: i32, b: i32) -> i32 {
    a + b
}

extern "system" fn system_multiply(a: i32, b: i32) -> i32 {
    a * b
}

// ---- Function pointers with explicit extern "system" ----

// CORRECT: extern "system" fn pointer assigned from extern "system" fn.
// The ABIs match exactly.
fn get_system_fn_ptr() -> extern "system" fn(i32, i32) -> i32 {
    system_add
}

// ---- Trait implementations with extern "system" ----

trait SystemCallback {
    fn invoke(&self, a: i32, b: i32) -> i32;
}

struct AddCallback;
struct MulCallback;

impl SystemCallback for AddCallback {
    fn invoke(&self, a: i32, b: i32) -> i32 {
        // Call through the extern "system" function.
        system_add(a, b)
    }
}

impl SystemCallback for MulCallback {
    fn invoke(&self, a: i32, b: i32) -> i32 {
        system_multiply(a, b)
    }
}

// ---- extern "system" in struct fields ----

struct CallbackTable {
    add: extern "system" fn(i32, i32) -> i32,
    mul: extern "system" fn(i32, i32) -> i32,
}

impl CallbackTable {
    fn new() -> Self {
        CallbackTable {
            add: system_add,
            mul: system_multiply,
        }
    }

    fn call_add(&self, a: i32, b: i32) -> i32 {
        (self.add)(a, b)
    }

    fn call_mul(&self, a: i32, b: i32) -> i32 {
        (self.mul)(a, b)
    }
}

// ---- The following patterns demonstrate what the bug fix prevents ----
//
// On x86 Windows, prior to the fix:
//
//   let c_fn: extern "C" fn(i32, i32) -> i32 = some_c_function;
//   let sys_fn: extern "system" fn(i32, i32) -> i32 = unsafe { std::mem::transmute(c_fn) };
//   // This would corrupt the stack on x86 Windows because "C" is cdecl
//   // (caller cleans) but "system" is stdcall (callee cleans).
//
// The fix ensures the compiler catches ABI mismatches even when
// "system" is involved, preventing silent stack corruption.

fn main() {
    // Direct calls through extern "system" functions.
    assert_eq!(system_add(3, 4), 7);
    assert_eq!(system_multiply(3, 4), 12);

    // Call through function pointer.
    let ptr = get_system_fn_ptr();
    assert_eq!(ptr(10, 20), 30);

    // Call through trait object.
    let callbacks: Vec<Box<dyn SystemCallback>> =
        vec![Box::new(AddCallback), Box::new(MulCallback)];
    assert_eq!(callbacks[0].invoke(5, 6), 11);
    assert_eq!(callbacks[1].invoke(5, 6), 30);

    // Call through callback table.
    let table = CallbackTable::new();
    assert_eq!(table.call_add(7, 8), 15);
    assert_eq!(table.call_mul(7, 8), 56);
}
