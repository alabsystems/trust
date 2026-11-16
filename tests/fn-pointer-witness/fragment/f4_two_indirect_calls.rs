//@ fn-ptr-witness: refuses
//! Two indirect calls, nested. Still no obligation.
pub fn twice(f: fn(u32) -> u32, x: u32) -> u32 { f(f(x)) }
