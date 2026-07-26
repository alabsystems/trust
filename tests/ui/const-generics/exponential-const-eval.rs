// Trust: regression test for exponential const evaluation (rust-lang/rust#150061, #922).
// Verifies that repeated references to the same const expression within a single
// evaluation context benefit from per-session caching, avoiding redundant work
// from repeated instance resolution, region erasure, and query key construction.
//@ check-pass

// Test 1: Same const item referenced multiple times in a single const body.
// The per-session cache ensures `LARGE_CONST` is only fully evaluated once
// even though it appears 4 times in the expression.
const LARGE_CONST: u64 = {
    let mut result = 0u64;
    let mut i = 0u64;
    while i < 1000 {
        result = result.wrapping_add(i);
        i += 1;
    }
    result
};

const QUAD: u64 = LARGE_CONST + LARGE_CONST + LARGE_CONST + LARGE_CONST;
const _: () = assert!(QUAD == LARGE_CONST * 4);

// Test 2: Nested const items that reference each other.
// Each level references the same sub-constant, and the cache prevents
// redundant evaluation at each level.
const A: u64 = 42;
const B: u64 = A + A + A;
const C: u64 = B + B + A;
const D: u64 = C + C + B + A;

const _: () = assert!(A == 42);
const _: () = assert!(B == 126);
const _: () = assert!(C == 294);
const _: () = assert!(D == 756);

// Test 3: Const fn that computes a value used many times.
const fn compute(n: u64) -> u64 {
    if n == 0 { 1 } else { n * compute(n - 1) }
}

const FACTORIAL_10: u64 = compute(10);
const _: () = assert!(FACTORIAL_10 == 3628800);

// Test 4: Multiple references to the same factorial in a single expression.
const TRIPLE_FACTORIAL: u64 = FACTORIAL_10 + FACTORIAL_10 + FACTORIAL_10;
const _: () = assert!(TRIPLE_FACTORIAL == 3628800 * 3);

fn main() {
    // Use the constants at runtime to prevent dead code elimination.
    assert_eq!(QUAD, 499500 * 4);
    assert_eq!(D, 756);
    assert_eq!(TRIPLE_FACTORIAL, 3628800 * 3);
}
