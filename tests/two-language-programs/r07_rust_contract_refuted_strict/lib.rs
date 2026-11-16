// The FALSE twin of r06: the build must be refused.
pub fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 3
{ x * 2 }
