// tRust regression test for rust-lang/rust#66220
//
// SOUNDNESS BUG: extern "C" functions returning bool can return values
// other than 0 or 1. The C ABI allows any non-zero value in the return
// register to represent "true," but Rust's bool has a validity invariant
// that only 0x00 and 0x01 are valid. When the C-side function returns,
// say, 0xFF in al, rustc assumes it's a valid bool and may use it in
// branch optimization, layout packing, or niche filling — all of which
// produce undefined behavior for values other than 0 or 1.
//
// The real-world impact: a C function returning a non-zero int as bool
// (common in C where any truthy value works) causes Rust to miscompile
// downstream code. For example, `Option<bool>` uses niche optimization
// and assumes only three bit patterns (0, 1, 2) are possible. A value
// of 0xFF breaks the niche.
//
// Status: open upstream. Rustc generates a `trunc i8 to i1` in LLVM for
// the return value, which silently discards upper bits, but the real issue
// is that no validity check is inserted at the FFI boundary.
//
// tRust must ensure that bool values crossing the FFI boundary are
// validated or that the ABI contract is enforced.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/66220

//@ check-pass

#![allow(dead_code)]

// Simulate the pattern: extern "C" function returning bool.
// The bug manifests when a C-side caller puts a non-{0,1} value in the
// return register, but we can demonstrate the Rust-side ABI shape here.

extern "C" fn returns_bool(x: u32) -> bool {
    x != 0
}

// The problematic pattern: using the bool return in niche-optimized types.
// If the bool came from C with value 0xFF, Option<bool> could have an
// invalid discriminant.
fn use_in_niche(val: bool) -> Option<bool> {
    Some(val)
}

// Another dangerous pattern: bool in match arms with exhaustiveness checking.
// The compiler assumes only true/false, so an invalid bool value can skip
// both arms entirely.
fn match_bool(val: bool) -> &'static str {
    match val {
        true => "yes",
        false => "no",
    }
}

// Callback pattern: passing a Rust fn returning bool to C code.
// C code may cast the return to int and compare against arbitrary values,
// but the Rust side must ensure the bool is valid.
type BoolCallback = extern "C" fn(u32) -> bool;

extern "C" fn get_callback() -> BoolCallback {
    returns_bool
}

fn main() {
    // Exercise the extern "C" bool return path
    let t = returns_bool(1);
    let f = returns_bool(0);
    assert!(t);
    assert!(!f);

    // Use in niche-optimized context
    let opt = use_in_niche(t);
    assert_eq!(opt, Some(true));

    // Use in exhaustive match
    assert_eq!(match_bool(t), "yes");
    assert_eq!(match_bool(f), "no");

    // Callback round-trip
    let cb = get_callback();
    assert!(cb(42));
}
