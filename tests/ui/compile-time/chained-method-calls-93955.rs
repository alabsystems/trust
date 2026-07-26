// Trust: regression test for compile-time bug rust-lang#93955
//
// Chained method calls on a builder-like pattern cause exponential compile
// time because each `.method()` call creates a new monomorphized type that
// the trait solver must resolve. With N chained calls, type inference must
// explore an exponentially growing set of possible method resolutions.
//
// The original report showed >10 minute compile times with ~20 chained calls.
// This test uses 15 chained calls, which should compile in seconds with
// proper caching but would take minutes without it.
//
// Upstream: https://github.com/rust-lang/rust/issues/93955
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// A builder pattern where each method returns a new wrapper type,
// forcing monomorphization at each step.
struct Builder<T>(T);

impl<T> Builder<T> {
    fn step(self) -> Builder<(T, i32)> {
        Builder((self.0, 0))
    }

    fn finish(self) -> T {
        self.0
    }
}

// Trait that must be resolved at each nesting level.
trait HasLen {
    fn len(&self) -> usize;
}

impl HasLen for i32 {
    fn len(&self) -> usize { 1 }
}

impl<A: HasLen, B: HasLen> HasLen for (A, B) {
    fn len(&self) -> usize { self.0.len() + self.1.len() }
}

fn main() {
    // Each .step() creates Builder<((...), i32)>, growing the type.
    // The trait solver must verify HasLen at each level.
    let result = Builder(0i32)
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .step()
        .finish();

    // Force trait resolution on the deeply nested type.
    assert!(result.len() > 0);
}
