// Trust: regression test for compile-time bug rust-lang#107250
//
// Quadratic behavior in region constraint processing occurs when functions
// have many lifetime-parameterized references. The region inference engine
// processes O(N^2) constraint pairs when N lifetime-bounded references
// interact through a shared constraint (e.g., all outliving a common region).
//
// The original report showed severe slowdowns with ~50+ region constraints.
// This test uses 20 lifetime-parameterized fields to exercise the quadratic
// region constraint propagation path without causing excessive compile time.
//
// Upstream: https://github.com/rust-lang/rust/issues/107250
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Struct with many lifetime-parameterized fields forces the region constraint
// solver to process pairwise relationships between all field lifetimes.
struct MultiRef<'a> {
    f0: &'a str,
    f1: &'a str,
    f2: &'a str,
    f3: &'a str,
    f4: &'a str,
    f5: &'a str,
    f6: &'a str,
    f7: &'a str,
    f8: &'a str,
    f9: &'a str,
    f10: &'a str,
    f11: &'a str,
    f12: &'a str,
    f13: &'a str,
    f14: &'a str,
    f15: &'a str,
    f16: &'a str,
    f17: &'a str,
    f18: &'a str,
    f19: &'a str,
}

// Function that takes and returns MultiRef, forcing region constraint
// propagation through the call graph.
fn process<'a>(m: &MultiRef<'a>) -> MultiRef<'a> {
    MultiRef {
        f0: m.f0, f1: m.f1, f2: m.f2, f3: m.f3, f4: m.f4,
        f5: m.f5, f6: m.f6, f7: m.f7, f8: m.f8, f9: m.f9,
        f10: m.f10, f11: m.f11, f12: m.f12, f13: m.f13, f14: m.f14,
        f15: m.f15, f16: m.f16, f17: m.f17, f18: m.f18, f19: m.f19,
    }
}

// Chain multiple calls to amplify region constraint processing.
fn chain<'a>(m: &MultiRef<'a>) -> MultiRef<'a> {
    let m1 = process(m);
    let m2 = process(&m1);
    let m3 = process(&m2);
    let m4 = process(&m3);
    let m5 = process(&m4);
    process(&m5)
}

fn main() {
    let s = "hello";
    let m = MultiRef {
        f0: s, f1: s, f2: s, f3: s, f4: s,
        f5: s, f6: s, f7: s, f8: s, f9: s,
        f10: s, f11: s, f12: s, f13: s, f14: s,
        f15: s, f16: s, f17: s, f18: s, f19: s,
    };
    let result = chain(&m);
    assert_eq!(result.f0, "hello");
}
