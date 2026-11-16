//@ trust-ladder: verifies
//! CONTROL. `{:?}` on a foundational type — core's own `Debug` impl.
pub fn f() { println!("{:?}", 1u32); }
