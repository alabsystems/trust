// Real-MIR arms for the OverflowNeg vacuity fix. Compiled with overflow checks ON.

// THE CANARY: `m` is `i32::MIN` for EVERY input, so `-m` overflows always.
#[inline(never)]
pub fn sentinel_negation_overflow_must_not_prove(x: i32) -> i32 {
    let m = (x & 0) | i32::MIN;
    -m
}

// THE SAFE CASE THAT MUST SURVIVE: one honest row must remain.
#[inline(never)]
pub fn provably_safe_negation(x: i32) -> i32 {
    if x > i32::MIN { -x } else { 0 }
}

// Undecided: nothing is known about `x`.
#[inline(never)]
pub fn unguarded_negation(x: i32) -> i32 {
    -x
}

// Two DISTINCT negated values, each with its own assert. A block-keyed skip
// would let one assert launder the other's obligation.
#[inline(never)]
pub fn two_distinct_negations(a: i32, b: i32) -> i32 {
    let p = -a;
    let q = -b;
    p.wrapping_add(q)
}

// Width sweep.
#[inline(never)]
pub fn negation_i8(x: i8) -> i8 {
    -x
}

#[inline(never)]
pub fn negation_i64(x: i64) -> i64 {
    -x
}

#[inline(never)]
pub fn negation_isize(x: isize) -> isize {
    -x
}

#[inline(never)]
pub fn negation_i128(x: i128) -> i128 {
    -x
}

// A PROJECTED negated operand: under overflow checks the value rustc compares
// with MIN and then negates is the `.0` field of the CheckedSub tuple.
#[inline(never)]
pub fn negation_of_projected_value(a: i32, b: i32) -> i32 {
    -(a - b)
}

// No MIR OverflowNeg assert to bind to.
#[inline(never)]
pub fn wrapping_negation(x: i32) -> i32 {
    x.wrapping_neg()
}

#[inline(never)]
pub fn float_negation(x: f64) -> f64 {
    -x
}

#[inline(never)]
pub fn abs_negation(x: i32) -> i32 {
    x.abs()
}
