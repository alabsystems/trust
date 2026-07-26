// I/O utility patterns: byte-level operations, formatting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn slice_len(data: &[u8]) -> usize {
    data.len()
}

pub fn first_byte(data: &[u8]) -> Option<u8> {
    data.first().copied()
}

pub fn last_byte(data: &[u8]) -> Option<u8> {
    data.last().copied()
}

pub fn count_byte(data: &[u8], target: u8) -> usize {
    data.iter().filter(|&&b| b == target).count()
}

pub fn hex_encode(data: &[u8]) -> String {
    data.iter().map(|b| format!("{b:02x}")).collect()
}
