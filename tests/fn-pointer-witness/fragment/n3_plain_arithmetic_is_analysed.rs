//@ fn-ptr-witness: refuses
//! POSITIVE CONTROL FOR THE INSTRUMENT. Proves the compiler under test DOES
//! mint obligations for this crate shape — so "no report" above is a fact about
//! fn-pointer calls, not about the measurement.
pub fn f(a: u32, b: u32) -> u32 { a + b }
