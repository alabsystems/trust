// tRust regression test for rust-lang/rust#63740
//
// SOUNDNESS BUG: On Windows ARM64 (aarch64-pc-windows-msvc), #[repr(C)]
// structs are not always passed according to the Windows ARM64 ABI (AAPCS64
// variant for Windows). Specifically, Homogeneous Floating-point Aggregates
// (HFAs) — structs containing 1-4 members of the same float type — should
// be passed in SIMD/FP registers, but rustc may pass them on the stack or
// in general-purpose registers instead.
//
// The Windows ARM64 ABI defines:
//   - HFA with 1-4 float members: pass in s0-s3 or d0-d3 registers
//   - Non-HFA structs <= 16 bytes: pass in x0-x7 (GPRs)
//   - Larger structs: pass by reference
//
// When rustc misclassifies an HFA as a non-HFA (or vice versa), the caller
// stores the struct in GPRs/stack while the callee reads from FP registers
// (or vice versa). This produces silent data corruption in cross-language FFI.
//
// The bug also affects return values: HFAs should be returned in FP registers
// but may be returned in GPRs, breaking any C/C++ code calling the Rust function.
//
// This is an architecture-specific ABI bug but the test pattern applies
// universally: repr(C) structs with homogeneous float members should have
// identical ABI to the equivalent C struct on all platforms.
//
// Status: partially fixed upstream for some cases, but edge cases remain
// (nested HFAs, transparent wrappers around HFAs, mixed-but-same-size floats).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Reference: https://github.com/rust-lang/rust/issues/63740

//@ check-pass

#![allow(dead_code)]

// ---- Homogeneous Floating-point Aggregates (HFAs) ----
//
// On ARM64 (both Windows and Unix), these should be passed in FP registers.

/// HFA with 2 f32 members — should be passed in s0, s1.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Point2D {
    x: f32,
    y: f32,
}

/// HFA with 4 f32 members — maximum HFA size, passed in s0-s3.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Rect {
    x: f32,
    y: f32,
    w: f32,
    h: f32,
}

/// HFA with 2 f64 members — should be passed in d0, d1.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Point2DDouble {
    x: f64,
    y: f64,
}

/// HFA with 4 f64 members — maximum HFA size for f64, passed in d0-d3.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct Matrix2x2 {
    m00: f64,
    m01: f64,
    m10: f64,
    m11: f64,
}

/// Nested HFA — the Windows ARM64 ABI should "flatten" this to 4 f32s.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
struct TwoPoints {
    a: Point2D,
    b: Point2D,
}

// ---- Functions with HFA parameters ----

extern "C" fn process_point(p: Point2D) -> Point2D {
    // BUG: On Windows ARM64, the caller may pass p in GPRs while this
    // function reads from FP registers (or vice versa).
    Point2D {
        x: p.x * 2.0,
        y: p.y * 2.0,
    }
}

extern "C" fn process_rect(r: Rect) -> f32 {
    r.x + r.y + r.w + r.h
}

extern "C" fn process_double_point(p: Point2DDouble) -> Point2DDouble {
    Point2DDouble {
        x: p.x + 1.0,
        y: p.y + 1.0,
    }
}

extern "C" fn process_nested_hfa(tp: TwoPoints) -> TwoPoints {
    // Nested HFAs are tricky: the ABI should flatten TwoPoints to
    // {f32, f32, f32, f32} and pass in s0-s3.
    TwoPoints {
        a: Point2D {
            x: tp.a.x + tp.b.x,
            y: tp.a.y + tp.b.y,
        },
        b: tp.b,
    }
}

// Return HFA — equally important: caller must read from FP registers.
extern "C" fn return_matrix() -> Matrix2x2 {
    Matrix2x2 {
        m00: 1.0,
        m01: 0.0,
        m10: 0.0,
        m11: 1.0,
    }
}

// ---- Mix of HFA and non-HFA parameters ----
// This tests the interaction between register classes: the integer parameter
// goes in a GPR, the HFA in FP registers. Getting the classification wrong
// for either one corrupts both.
extern "C" fn mixed_params(id: u64, pos: Point2D, scale: f64) -> f64 {
    let _ = id;
    (pos.x as f64 + pos.y as f64) * scale
}

fn main() {
    // Test HFA pass-through.
    let p = Point2D { x: 1.0, y: 2.0 };
    let p2 = process_point(p);
    assert_eq!(p2, Point2D { x: 2.0, y: 4.0 });

    // Test 4-member HFA.
    let r = Rect {
        x: 1.0,
        y: 2.0,
        w: 3.0,
        h: 4.0,
    };
    let sum = process_rect(r);
    assert!((sum - 10.0).abs() < f32::EPSILON);

    // Test f64 HFA.
    let dp = Point2DDouble { x: 10.0, y: 20.0 };
    let dp2 = process_double_point(dp);
    assert_eq!(dp2, Point2DDouble { x: 11.0, y: 21.0 });

    // Test nested HFA.
    let tp = TwoPoints {
        a: Point2D { x: 1.0, y: 2.0 },
        b: Point2D { x: 3.0, y: 4.0 },
    };
    let tp2 = process_nested_hfa(tp);
    assert_eq!(tp2.a, Point2D { x: 4.0, y: 6.0 });

    // Test HFA return value.
    let mat = return_matrix();
    assert_eq!(mat.m00, 1.0);
    assert_eq!(mat.m11, 1.0);

    // Test mixed HFA + integer params.
    let result = mixed_params(999, Point2D { x: 3.0, y: 4.0 }, 2.0);
    assert!((result - 14.0).abs() < f64::EPSILON);
}
