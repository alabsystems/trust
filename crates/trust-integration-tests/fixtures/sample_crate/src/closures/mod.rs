// Closure and iterator patterns.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn map_double(v: &[i32]) -> Vec<i32> {
    v.iter().map(|x| x * 2).collect()
}

pub fn filter_positive(v: &[i32]) -> Vec<i32> {
    v.iter().copied().filter(|x| *x > 0).collect()
}

pub fn any_negative(v: &[i32]) -> bool {
    v.iter().any(|x| *x < 0)
}

pub fn all_positive(v: &[i32]) -> bool {
    v.iter().all(|x| *x > 0)
}

pub fn take_while_positive(v: &[i32]) -> Vec<i32> {
    v.iter().copied().take_while(|x| *x > 0).collect()
}

pub fn fold_concat(v: &[&str]) -> String {
    v.iter().fold(String::new(), |mut acc, s| {
        acc.push_str(s);
        acc
    })
}

pub fn chain_vecs(a: &[i32], b: &[i32]) -> Vec<i32> {
    a.iter().chain(b.iter()).copied().collect()
}

pub fn partition_even_odd(v: &[i32]) -> (Vec<i32>, Vec<i32>) {
    v.iter().copied().partition(|x| x % 2 == 0)
}
