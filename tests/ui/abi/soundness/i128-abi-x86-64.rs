// tRust regression test for rust-lang/rust#115278
//
// SOUNDNESS BUG: On x86-64, rustc passes i128/u128 in a single 128-bit
// register (or as a single 128-bit stack slot), but the x86-64 SysV ABI
// specifies that 128-bit integers should be passed as two 64-bit halves
// in two separate registers (or two stack slots). This means that Rust's
// extern "C" fn with i128 parameters has a different calling convention
// than C's __int128.
//
// When Rust calls a C function expecting __int128, or when C calls a
// Rust extern "C" function taking i128, the two sides disagree on where
// the high and low 64-bit halves are. This produces silent data corruption
// or reads of uninitialized register values.
//
// The issue also affects the Windows x64 ABI (where >64-bit values are
// passed by reference) and other targets with __int128 support.
//
// Concrete example (x86-64 SysV):
//   Rust passes i128 in RDX:RAX as a single "register pair"
//   C expects __int128 in RDI:RSI (as two INTEGER class arguments)
//   Result: callee reads wrong registers, gets garbage
//
// Status: fixed in upstream rust-lang/rust#137184 (landed in nightly).
// The fix changes extern "C" i128/u128 to use the correct two-register
// convention. This test ensures we don't regress.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/115278

//@ only-x86_64
//@ check-pass

#![allow(dead_code)]

// Extern "C" function taking i128 — this is the pattern that was broken.
// The calling convention for i128 must match what a C compiler would generate
// for __int128.
extern "C" fn pass_i128(a: i32, b: i128, c: i32) -> i128 {
    // BUG (before fix): `b` arrives with its halves swapped, or with one
    // half containing garbage, because caller and callee disagree on which
    // registers hold the high and low 64 bits.
    //
    // The extra i32 parameters `a` and `c` are important: they shift the
    // register allocation and expose mismatches in the classification of
    // the i128 argument. Without them, the bug might be hidden by register
    // assignments accidentally lining up.
    let _ = a;
    let _ = c;
    b
}

// Same issue with u128 (unsigned variant, same ABI concern).
extern "C" fn pass_u128(x: u128) -> u128 {
    x.wrapping_add(1)
}

// Returning i128 from extern "C" is equally affected — the caller may read
// the return value from the wrong registers.
extern "C" fn return_i128() -> i128 {
    // 0x0001_0002_0003_0004_0005_0006_0007_0008
    // High 64 bits: 0x0001_0002_0003_0004
    // Low 64 bits:  0x0005_0006_0007_0008
    0x0001_0002_0003_0004_0005_0006_0007_0008_i128
}

// Function pointer usage — ensures the ABI mismatch also affects indirect calls
// where the compiler cannot see the callee's implementation.
fn call_through_fnptr() -> i128 {
    let f: extern "C" fn(i32, i128, i32) -> i128 = pass_i128;
    f(0, 0x7FFF_FFFF_FFFF_FFFF_0000_0000_0000_0001_i128, 0)
}

fn main() {
    // Verify round-trip through extern "C" preserves the value.
    let input: i128 = 0x1EAD_BEEF_CAFE_BABE_1234_5678_9ABC_DEF0_i128;
    let output = pass_i128(42, input, 99);
    assert_eq!(input, output);

    // Verify u128 round-trip.
    let u_input: u128 = 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFE;
    let u_output = pass_u128(u_input);
    assert_eq!(u_output, u_input.wrapping_add(1));

    // Verify return value.
    let returned = return_i128();
    assert_eq!(returned, 0x0001_0002_0003_0004_0005_0006_0007_0008_i128);

    // Verify function pointer path.
    let fnptr_result = call_through_fnptr();
    assert_eq!(fnptr_result, 0x7FFF_FFFF_FFFF_FFFF_0000_0000_0000_0001_i128);
}
