// Pattern matching and enum operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn classify(n: i32) -> &'static str {
    if n < 0 {
        "negative"
    } else if n == 0 {
        "zero"
    } else {
        "positive"
    }
}

pub fn day_kind(day: u8) -> &'static str {
    match day {
        1..=5 => "weekday",
        6 | 7 => "weekend",
        _ => "invalid",
    }
}

pub fn is_even(n: i32) -> bool {
    n % 2 == 0
}

pub fn sign(n: i64) -> i64 {
    match n.cmp(&0) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

pub fn bool_to_int(b: bool) -> i32 {
    if b { 1 } else { 0 }
}

pub fn grade(score: u32) -> &'static str {
    match score {
        90..=100 => "A",
        80..=89 => "B",
        70..=79 => "C",
        60..=69 => "D",
        _ => "F",
    }
}
