// Trust: regression test for compile-time bug rust-lang#72408
//
// Nested closures cause exponential compilation time because closures include
// captured types twice in the type tree (once for the closure struct layout,
// once for the Fn impl). Each additional wrapping layer doubles the type tree
// size, causing O(2^N) growth.
//
// The original report used 30 levels which hit the type-length limit. This
// test uses 12 levels — enough to exercise the code path without exceeding
// limits or causing unacceptable compile times.
//
// Upstream: https://github.com/rust-lang/rust/issues/72408
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

fn dup<F: Fn(i32) -> i32>(f: F) -> impl Fn(i32) -> i32 {
    move |a| f(2 * a)
}

pub fn main() {
    let f = |a: i32| a;
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    let f = dup(f);
    // 12 levels: each doubles the type tree. Without deduplication, the
    // compiler must process O(2^12) = 4096 type nodes. Should compile in
    // under a few seconds.
    let _ = f(1);
}
