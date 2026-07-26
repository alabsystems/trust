// Trust: regression test for compile-time exponential trait resolution
//
// Nested trait bounds with multiple layers of generic constraints cause
// exponential trait obligation resolution. When trait A<T> requires B<T>,
// which requires C<T>, and each bound spawns multiple sub-obligations,
// the obligation forest grows exponentially.
//
// This test exercises the pattern where a chain of traits with associated
// types each require the previous level, creating multiplicative obligation
// growth. At 8 nesting levels with 2 associated types each, the naive
// solver would evaluate O(2^8) = 256 obligations. With proper caching,
// this should be linear.
//
// Inspired by patterns from rust-lang#74170 and similar trait resolution bugs.
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

trait Level<T> {
    type Out1;
    type Out2;
    fn compute(&self, val: T) -> T;
}

// Base case: unit type implements Level for any T.
impl<T> Level<T> for () {
    type Out1 = ();
    type Out2 = ();
    fn compute(&self, val: T) -> T { val }
}

// Wrapper that nests one level deeper, requiring the inner type to
// implement Level with specific associated type constraints.
struct Wrap<Inner>(Inner);

impl<T, Inner> Level<T> for Wrap<Inner>
where
    Inner: Level<T, Out1 = (), Out2 = ()>,
{
    type Out1 = ();
    type Out2 = ();
    fn compute(&self, val: T) -> T { self.0.compute(val) }
}

// Each nesting of Wrap<Wrap<...>> doubles the obligation tree because
// both Out1 and Out2 constraints must be verified at each level.
fn require_level<T, L: Level<T, Out1 = (), Out2 = ()>>(l: &L, val: T) -> T {
    l.compute(val)
}

pub fn main() {
    // 8 levels of nesting
    let l = ();
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);
    let l = Wrap(l);

    let result = require_level(&l, 42i32);
    assert_eq!(result, 42);
}
