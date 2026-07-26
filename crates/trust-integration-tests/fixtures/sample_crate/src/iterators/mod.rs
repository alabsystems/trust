// Iterator adapter patterns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn enumerate_sum(v: &[i32]) -> usize {
    v.iter().enumerate().map(|(i, _)| i).sum()
}

pub fn zip_sum(a: &[i32], b: &[i32]) -> Vec<i32> {
    a.iter().zip(b.iter()).map(|(x, y)| x + y).collect()
}

pub fn flat_map_split(v: &[String]) -> Vec<String> {
    v.iter()
        .flat_map(|s| s.split(',').map(String::from))
        .collect()
}

pub fn skip_take(v: &[i32], skip: usize, take: usize) -> Vec<i32> {
    v.iter().skip(skip).take(take).copied().collect()
}

pub fn step_by_two(v: &[i32]) -> Vec<i32> {
    v.iter().step_by(2).copied().collect()
}
