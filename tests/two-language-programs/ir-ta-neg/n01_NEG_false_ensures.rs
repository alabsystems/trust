// Negative twin of rust.contracts: the SAME function with a FALSE postcondition. The strict
// (default) verification lane must refuse the build, naming the postcondition.
pub fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 3
{ x * 2 }
