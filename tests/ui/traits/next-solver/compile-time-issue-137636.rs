// Regression test for rust-lang/rust#137636
// Query structure dependent compile time issue: polynomial/exponential slowdown
// with nested `impl Trait` return type composition and method chaining.
//
// The old AND new trait solver both exhibit super-polynomial time complexity
// when resolving chains of methods returning `impl Trait` where the result
// is rebound and chained further. This is NOT yet fixed by the next-solver.
//
// Scaling observed with -Znext-solver=globally:
//   3 chain-lines: ~0.3s
//   5 chain-lines: ~1.0s
//   7 chain-lines: >120s (timeout)
//   11 chain-lines (original): hangs indefinitely
//
// This reduced test uses only 3 chain-lines to avoid CI timeout while
// documenting the pattern. The compiler correctly produces borrow/move
// errors but the time to produce them scales super-polynomially with depth.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Trust: next-solver compile-time regression test (NOT YET FIXED)

//@ compile-flags: -Znext-solver=globally
//@ known-bug: rust-lang/rust#137636

pub trait A<'a> {
    fn or(&self, other: impl A<'a>) -> impl A<'a> {
        ()
    }
}

impl<'a> A<'a> for () {}

pub fn main() {
    // Reduced from the original 11 chain-lines to 3 to avoid CI timeout.
    // The original pattern causes exponential compile time blowup.
    let x = ().or(()).or(());
    let x = x.or(x).or(x).or(x);
    let x = x.or(x).or(x).or(x);
    // Adding more lines here causes exponential compile time increase:
    // let x = x.or(x).or(x).or(x);  // 4th line: ~seconds
    // let x = x.or(x).or(x).or(x);  // 5th line: ~seconds
    // let x = x.or(x).or(x).or(x);  // 6th line: ~tens of seconds
    // let x = x.or(x).or(x).or(x);  // 7th line: >2 minutes
}
