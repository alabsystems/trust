//@ fn-ptr-witness: refuses
//! WIDER THAN THE FIXTURE RECORDS. The pointer lives in a struct field, so not
//! even a local reaching-definition could pin it, and it still builds green.
pub struct T { pub f: fn(u32) -> u32 }
pub fn call(t: &T, x: u32) -> u32 { (t.f)(x) }
