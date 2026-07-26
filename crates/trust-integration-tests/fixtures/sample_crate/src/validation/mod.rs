// Input validation patterns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn is_ascii_alpha(c: char) -> bool {
    c.is_ascii_alphabetic()
}

pub fn is_ascii_digit(c: char) -> bool {
    c.is_ascii_digit()
}

pub fn is_valid_port(port: u32) -> bool {
    port > 0 && port <= 65535
}

pub fn is_valid_percentage(val: f64) -> bool {
    (0.0..=100.0).contains(&val)
}

pub fn sanitize_index(index: usize, len: usize) -> Option<usize> {
    if index < len { Some(index) } else { None }
}

#[requires(max > 0)]
pub fn clamp_to_max(val: usize, max: usize) -> usize {
    if val > max { max } else { val }
}
