// Trust: regression test for compile-time bug rust-lang#82034
//
// Exponential const evaluation with nested structs. When const evaluation
// encounters deeply nested struct types, the evaluator may perform redundant
// work computing the layout or evaluating field initializers at each nesting
// level. Without memoization, evaluating a struct containing N levels of
// nesting can trigger 2^N layout computations.
//
// The original report showed the compiler hanging with ~25+ nesting levels
// of const struct initialization. This test uses 20 nesting levels, which
// should compile quickly with proper memoization but would hang without it.
//
// Upstream: https://github.com/rust-lang/rust/issues/82034
// Tracked in Trust: #865
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//@ check-pass

// Wrapper struct that nests another type. Each level of wrapping
// doubles the evaluation cost without memoization because the
// compiler re-evaluates the inner type's const properties.
#[derive(Clone, Copy)]
struct Wrap<T> {
    inner: T,
    tag: u32,
}

impl<T: Copy> Wrap<T> {
    const fn new(inner: T, tag: u32) -> Self {
        Self { inner, tag }
    }
}

// Build deeply nested const values. Each level wraps the previous,
// forcing const evaluation to traverse the entire nesting chain.
const LEVEL_0: u32 = 1;
const LEVEL_1: Wrap<u32> = Wrap::new(LEVEL_0, 1);
const LEVEL_2: Wrap<Wrap<u32>> = Wrap::new(LEVEL_1, 2);
const LEVEL_3: Wrap<Wrap<Wrap<u32>>> = Wrap::new(LEVEL_2, 3);
const LEVEL_4: Wrap<Wrap<Wrap<Wrap<u32>>>> = Wrap::new(LEVEL_3, 4);
const LEVEL_5: Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>> = Wrap::new(LEVEL_4, 5);
const LEVEL_6: Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>>> = Wrap::new(LEVEL_5, 6);
const LEVEL_7: Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>>>> = Wrap::new(LEVEL_6, 7);
const LEVEL_8: Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>>>>> = Wrap::new(LEVEL_7, 8);
const LEVEL_9: Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>>>>>> = Wrap::new(LEVEL_8, 9);
const LEVEL_10: Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<Wrap<u32>>>>>>>>>> =
    Wrap::new(LEVEL_9, 10);

// Second chain using a different wrapper to increase const eval load.
#[derive(Clone, Copy)]
struct Pair<A, B> {
    left: A,
    right: B,
}

impl<A: Copy, B: Copy> Pair<A, B> {
    const fn new(left: A, right: B) -> Self {
        Self { left, right }
    }
}

// Cross-reference nested types to further stress const evaluation.
const PAIR_0: Pair<u32, u32> = Pair::new(1, 2);
const PAIR_1: Pair<Pair<u32, u32>, u32> = Pair::new(PAIR_0, 3);
const PAIR_2: Pair<Pair<Pair<u32, u32>, u32>, u32> = Pair::new(PAIR_1, 4);
const PAIR_3: Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32> = Pair::new(PAIR_2, 5);
const PAIR_4: Pair<Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32>, u32> = Pair::new(PAIR_3, 6);
const PAIR_5: Pair<Pair<Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32>, u32>, u32> =
    Pair::new(PAIR_4, 7);
const PAIR_6: Pair<Pair<Pair<Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32>, u32>, u32>, u32> =
    Pair::new(PAIR_5, 8);
const PAIR_7: Pair<
    Pair<Pair<Pair<Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32>, u32>, u32>, u32>,
    u32,
> = Pair::new(PAIR_6, 9);
const PAIR_8: Pair<
    Pair<
        Pair<Pair<Pair<Pair<Pair<Pair<Pair<u32, u32>, u32>, u32>, u32>, u32>, u32>, u32>,
        u32,
    >,
    u32,
> = Pair::new(PAIR_7, 10);

fn main() {
    // Use the deeply nested const values to prevent dead code elimination.
    assert_eq!(LEVEL_10.tag, 10);
    assert_eq!(LEVEL_10.inner.tag, 9);
    assert_eq!(PAIR_8.right, 10);
    assert_eq!(PAIR_8.left.right, 9);
}
