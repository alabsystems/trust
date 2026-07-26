// Async functions exercising the state machine transform pattern.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub async fn async_identity(x: u32) -> u32 {
    x
}

pub async fn async_add(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub async fn async_option(x: Option<u32>) -> u32 {
    x.unwrap_or(0)
}

pub async fn async_result(x: Result<u32, ()>) -> u32 {
    x.unwrap_or(0)
}

pub async fn async_vec_len(v: Vec<u32>) -> usize {
    v.len()
}
