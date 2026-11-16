// The first thing any program does, under verification ON.
fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 2
{ x * 2 }
fn main() { println!("{}", double(21)); }
