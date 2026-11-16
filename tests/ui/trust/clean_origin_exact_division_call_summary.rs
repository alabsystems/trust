//@ needs-trust-verify
//@ edition: 2021
//@ revisions: mask shr div rem wrong_rem bitor_unmodeled
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[mask] check-pass
//@[shr] check-pass
//@[div] check-pass
//@[rem] check-pass
//@[wrong_rem] check-fail
//@[bitor_unmodeled] check-fail
//! **A caller of an exact-division raw-binop island `def` gets its value (Trust,
//! 2026-09-28).**
//!
//! `def low_bit x := x &&& 1` is emitted as one `BitAnd` and gate-checked. Its
//! result was havocked at the caller, so `table[low_bit(i) as usize]` over a
//! two-element table was refuted (measured with `verified_counterexample = true`
//! in the two-language probe sweep, m11a).
//!
//! Now four forms carry an exact quotient or remainder by a positive literal:
//! `&` with a `2^k - 1` mask (`x % 2^k`), `>>` by an in-range numeral
//! (`x / 2^k`), and `/` and `%` by a positive numeral. The injection filter
//! admits that shape past its machine-arithmetic check
//! (`formula_is_exact_division_by_positive_literal`): a positive literal divisor
//! can neither panic nor overflow, and truncated division is Rust's.
//!
//! * `mask`, `shr`, `div`, `rem`: POSITIVE.
//! * `wrong_rem`: `x % 7` indexes a SIX-element table, and must stay refuted.
//! * `bitor_unmodeled`: `x ||| 1` is outside the modeled forms, so its exact
//!   value does not reach the caller and a claim that needs it (`result` is odd)
//!   stays unproved. Its return interval does reach it since 2026-09-30
//!   (`compute_return_interval_summaries`: the codegened body's `x | 1` is at least
//!   1), which is why the claim is not the weaker `result >= 1`.

#[cfg(mask)]
clean {
    def low_bit (x : UInt64) : UInt64 := x &&& 1
}

#[cfg(mask)]
pub fn pick(table: [u32; 2], i: u64) -> u32 {
    table[low_bit(i) as usize]
}

#[cfg(shr)]
clean {
    def half (x : UInt32) : UInt32 := x >>> 1
}

#[cfg(shr)]
pub fn call_half(a: u32) -> u32
    ensures result <= a
{
    half(a)
}

#[cfg(div)]
clean {
    def tenth (x : UInt64) : UInt64 := x / 10
}

#[cfg(div)]
pub fn call_tenth(a: u64) -> u64
    ensures result <= a
{
    tenth(a)
}

#[cfg(any(rem, wrong_rem))]
clean {
    def mod7 (x : UInt64) : UInt64 := x % 7
}

#[cfg(rem)]
pub fn day(names: [u8; 7], n: u64) -> u8 {
    names[mod7(n) as usize]
}

#[cfg(wrong_rem)]
pub fn day(names: [u8; 6], n: u64) -> u8 {
    //[wrong_rem]~^ ERROR Trust
    names[mod7(n) as usize]
}

#[cfg(bitor_unmodeled)]
clean {
    def set_low (x : UInt64) : UInt64 := x ||| 1
}

#[cfg(bitor_unmodeled)]
pub fn call_set_low(a: u64) -> u64
    ensures result % 2 == 1
{
    //[bitor_unmodeled]~^^^ ERROR Trust
    set_low(a)
}
