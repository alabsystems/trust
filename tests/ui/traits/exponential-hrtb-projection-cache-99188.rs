// Trust: regression test for compile-time bug rust-lang#99188
//
// Missing caching for HRTB projection equality bounds causes exponential
// compile time. Each additional reference layer multiplies time by ~4x
// (correlating with the 4 associated types constrained simultaneously).
//
// Originally reduced from production code using the `tower` crate (its
// `Service` trait has `Response` and `Error` associated types).
//
// The root cause is that `ProjectionCacheKey::from_poly_projection_predicate`
// returns None for predicates with bound variables (HRTB), skipping the
// cache entirely. This forces re-evaluation of the same obligations
// exponentially many times.
//
// This test uses depth 7 (takes <1s) to avoid CI timeouts. Depth 10 takes
// ~50s without the fix, demonstrating clear exponential growth.
//
// Upstream: https://github.com/rust-lang/rust/issues/99188
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

trait Trait<'a> {
    type A;
    type B;
    type C;
    type D;

    fn method() {}
}

impl<T> Trait<'_> for &'_ T
where
    for<'x> T: Trait<'x, A = (), B = (), C = (), D = ()>,
{
    type A = ();
    type B = ();
    type C = ();
    type D = ();
}

impl Trait<'_> for () {
    type A = ();
    type B = ();
    type C = ();
    type D = ();
}

pub fn main() {
    // Depth 7: should compile in under a second.
    // Without HRTB projection caching, each layer adds ~4x time.
    <&&&&&&&() as Trait>::method();
}
