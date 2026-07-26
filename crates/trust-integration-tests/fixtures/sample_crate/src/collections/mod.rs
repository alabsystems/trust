// Collection operations: Vec, HashMap, sorting.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::HashMap;

pub fn vec_sum(v: &[i64]) -> i64 {
    v.iter().sum()
}

pub fn vec_product(v: &[i64]) -> i64 {
    v.iter().product()
}

pub fn vec_max(v: &[i32]) -> Option<i32> {
    v.iter().copied().max()
}

pub fn vec_min(v: &[i32]) -> Option<i32> {
    v.iter().copied().min()
}

pub fn dedup_sorted(v: &mut Vec<i32>) {
    v.dedup();
}

pub fn word_frequencies(words: &[&str]) -> HashMap<String, usize> {
    let mut freq = HashMap::new();
    for &word in words {
        *freq.entry(word.to_string()).or_insert(0) += 1;
    }
    freq
}
