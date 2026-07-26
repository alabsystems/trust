// Minimal test binary for reverse compilation POC.
// Compile: rustc --edition 2021 -O -o /tmp/test_target examples/test_target.rs
// Strip:   strip /tmp/test_target
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#[unsafe(no_mangle)]
pub fn add_two(a: u64, b: u64) -> u64 {
    a + b
}

#[unsafe(no_mangle)]
pub fn is_positive(x: i64) -> bool {
    x > 0
}

fn main() {
    let result = add_two(3, 4);
    println!("add_two(3, 4) = {result}");
    println!("is_positive(5) = {}", is_positive(5));
    println!("is_positive(-1) = {}", is_positive(-1));
}
