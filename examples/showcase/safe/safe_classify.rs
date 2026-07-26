// examples/showcase/safe/safe_classify.rs — Safe exhaustive match.
//
// Safe variant of verify_unreachable.rs.
// The buggy version uses unreachable!() for values > 100, which panics
// at runtime. This safe version handles all u32 values with an
// explicit "large" arm, making the match truly exhaustive.
//
// Trust expected result: PROVED (no Unreachable path reachable)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn classify(x: u32) -> &'static str {
    match x {
        0 => "zero",
        1..=100 => "small",
        101..=1000 => "medium",
        _ => "large", // SAFE: all values handled without unreachable!()
    }
}

fn main() {
    println!("classify(0) = {}", classify(0));
    println!("classify(50) = {}", classify(50));
    println!("classify(500) = {}", classify(500));
    println!("classify(10000) = {}", classify(10000));
}
