// Rust contracts in the compiler grammar, verified fail-closed (default policy).
pub fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 2
{ x * 2 }
