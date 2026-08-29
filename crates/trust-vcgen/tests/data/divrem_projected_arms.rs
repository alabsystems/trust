// Source of the REAL extracted-MIR fixtures for the projected-operand
// `Overflow(Div|Rem)` vacuity fix. Dumped verbatim with
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> divrem_projected_arms.rs
//
// so every fixture is the compiler's own verification input, not an
// approximation of it. Committed beside the JSON so each row re-derives.
#![allow(dead_code)]

// THE DEFECT. The dividend reaching the `Div` is `_3.0`, the value field of the
// `CheckedAdd` tuple, so the `Eq(_3.0, INT_MIN)` conjunct of the overflow cond
// compares a PROJECTED place. Two `arithmetic overflow (Div)` rows before the
// fix; the statement-lane one is `NOT _7 AND _7`, UNSAT by construction.
pub fn projected_dividend_div(x: i32, b: i32) -> i32 {
    let a = x + 1;
    a / b
}

// The divisor side of the same shape: `Eq(_3.0, -1)` compares a projected place.
pub fn projected_divisor_div(a: i32, y: i32) -> i32 {
    let b = y + 1;
    a / b
}

// Both operands projected — the genuinely-false `i32::MIN / -1` canary shape.
pub fn projected_both_div(x: i32, y: i32) -> i32 {
    let a = x + 1;
    let b = y - 1;
    a / b
}

// The `Rem` twin: same lowering, `Overflow(Rem)` + `RemainderByZero`.
pub fn projected_both_rem(x: i32, y: i32) -> i32 {
    let a = x + 1;
    let b = y - 1;
    a % b
}

// Two divisions, two chains. A skip keyed on the BLOCK rather than on the
// OPERANDS drops one of two real obligations.
pub fn two_distinct_projected_divisors(x: i32, y: i32, z: i32) -> i32 {
    let a = x + 1;
    let b = y + 1;
    let c = z + 1;
    (a / b) ^ (a / c)
}

// CONTROL. Identical block depth, identical assert-chain length, identical
// sole-entry topology, `Div` in the same block position — the ONE difference is
// that the dividend `_5` is a PLAIN local. One row before the fix and one after:
// this arm isolates the projection as the discriminator, and it goes red if the
// suppression is deleted wholesale.
pub fn plain_dividend_deep_div(x: i32, s: u32, b: i32) -> i32 {
    let a = x << s;
    a / b
}

// SAFE CASE, PROJECTED. `(x & 1) + 1` is 1 or 2, so this division provably
// cannot overflow — and the surface must still carry exactly one REAL,
// refutable obligation for the discharge lanes to prove. A suppression that
// deleted this is a lost recovery, not a fix.
pub fn provably_safe_projected_dividend_div(x: i32, b: i32) -> i32 {
    let a = (x & 1) + 1;
    a / b
}

// SAFE CASE, CONSTANT DIVISOR. Its cond is a const/const `Eq` that no binding
// claims, so it is two rows before AND after; pinning it that way is the point.
pub fn provably_safe_projected_div(x: i32) -> i32 {
    let a = x | 1;
    a / 3
}

// The CONSTANT compared value that is suppressed TODAY and must stay suppressed:
// `i32::MIN / y` lowers to `_4 = Eq(const INT_MIN, const INT_MIN)`. A binder that
// admitted only PLACES would resurrect the vacuous row at the span of a
// genuinely-false division.
pub fn const_min_dividend_div(y: i32) -> i32 {
    i32::MIN / y
}

pub fn const_min_dividend_rem(y: i32) -> i32 {
    i32::MIN % y
}

// The const-identity arm: `7 / y` lowers to `_4 = Eq(const 7, const INT_MIN)`,
// whose constant does NOT match, so no binding exists and both rows stay.
pub fn nonmin_const_dividend_div(y: i32) -> i32 {
    7 / y
}

// UNSIGNED: no `Overflow(Div)` obligation exists at all, and the divzero row is
// deduplicated by `v2_divzero_assert_exactly_bound`. Untouched in both directions.
pub fn projected_unsigned_div(x: u32, y: u32) -> u32 {
    let a = x + 1;
    let b = y - 1;
    a / b
}

// `a.div_euclid(b)` has no MIR assert to bind to — no suppression can reach it.
pub fn unguarded_call_projected_div(x: i32, b: i32) -> i32 {
    let a = x + 1;
    a.div_euclid(b)
}

// PROJECTION-SHAPE ARMS. rustc copies a deref/element read into a projection-free
// temporary before comparing it (measured: `_3 = Use (*_1)` / `_4 = Use _1[_2]`),
// so these compile to the ordinary plain-local shape. They exist as the REAL,
// well-typed bases the `Index`/`Deref` forged arms retarget the comparison and the
// division onto — a `_1[_2]` compared value only types because `_1` really is
// `[i32; 4]` here.
pub fn deref_operand_div(p: &i32, q: &i32) -> i32 {
    *p / *q
}

pub fn index_operand_div(a: [i32; 4], i: usize, j: usize) -> i32 {
    a[i] / a[j]
}
