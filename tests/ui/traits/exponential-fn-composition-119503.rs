// Trust: regression test for compile-time bug rust-lang#119503
//
// Each additional `let x = Apply(x, drop);` statement doubles compilation
// time due to exponential type growth: `drop` has an early-bound generic
// parameter, making `type X2 = Apply<X1, drop::<X1>>` grow exponentially.
//
// This test uses a reduced depth (10 levels) to avoid hanging in CI while
// still exercising the problematic code path. The original report used 16+
// levels which caused multi-minute compilation.
//
// Upstream: https://github.com/rust-lang/rust/issues/119503
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

struct Apply<X, F: Fn(X)>(X, F);

pub fn main() {
    let x = &();
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let x = Apply(x, drop);
    let _ = x;
}
