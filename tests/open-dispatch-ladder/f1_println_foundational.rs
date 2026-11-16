//@ trust-ladder: verifies
//! CONTROL. Formatting a foundational type through the full `println!` machinery
//! verifies. If this ever reads `refuses`, the ladder is measuring a broken
//! toolchain, not the open-dispatch gate.
pub fn f() { println!("{}", 1u32); }
