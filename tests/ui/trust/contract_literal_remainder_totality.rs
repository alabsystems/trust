//@ needs-trust-verify
//@ edition: 2021
//@ revisions: unsigned signed wrong zero negative_one symbolic computed out_of_range division
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[unsigned] check-pass
//@[signed] check-pass
//@[wrong] check-fail
//@[zero] check-fail
//@[negative_one] check-fail
//@[symbolic] check-fail
//@[computed] check-fail
//@[out_of_range] check-fail
//@[division] check-fail
//! Trust: authored remainder clauses use declared-width Rust semantics. A
//! positive literal divisor is total, including for a signed MIN dividend.
//! The body is an identity so refusals come from the authored clause rather
//! than from an unrelated runtime division assertion. True symbolic/computed
//! remainder bounds and true division bounds must still stay unsupported.

#[cfg(unsigned)]
pub fn unsigned_bound(x: u32) -> u32
    ensures result == x && x % 2 < 2
{
    x
}

#[cfg(signed)]
pub fn signed_bound(x: i32) -> i32
    ensures result == x && x % 2 >= -1 && x % 2 <= 1 && (x >= 0 || x % 2 <= 0)
{
    x
}

#[cfg(wrong)]
pub fn wrong_bound(x: u32) -> u32
    ensures x % 2 == 0
{
    //[wrong]~^^^ ERROR Trust
    x
}

#[cfg(zero)]
pub fn zero_divisor(x: u32) -> u32
    ensures x % 0 == 0
{
    //[zero]~^^^ ERROR Trust
    x
}

#[cfg(negative_one)]
pub fn signed_overflow_divisor(x: i32) -> i32
    ensures x % -1 == 0
{
    //[negative_one]~^^^ ERROR Trust
    x
}

#[cfg(symbolic)]
pub fn symbolic_divisor(x: u32, divisor: u32) -> u32
    requires divisor == 2
    ensures x % divisor < 2
{
    //[symbolic]~^^^^ ERROR Trust
    x
}

#[cfg(computed)]
pub fn computed_divisor(x: u32) -> u32
    ensures x % (1 + 1) < 2
{
    //[computed]~^^^ ERROR Trust
    x
}

#[cfg(out_of_range)]
pub fn unrepresentable_divisor(x: u8) -> u8
    ensures x % 256 <= x
{
    //[out_of_range]~^^^ ERROR Trust
    x
}

#[cfg(division)]
pub fn division_stays_refused(x: u32) -> u32
    ensures x / 2 <= x
{
    //[division]~^^^ ERROR Trust
    x
}
