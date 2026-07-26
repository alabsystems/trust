// Algorithms: search, sort, numeric algorithms.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn gcd(a: u64, b: u64) -> u64 {
    let (mut a, mut b) = (a, b);
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn fibonacci(n: u32) -> u64 {
    if n <= 1 {
        return n as u64;
    }
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 2..=n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
    }
    b
}

pub fn binary_search(haystack: &[i32], needle: i32) -> Option<usize> {
    let (mut lo, mut hi) = (0, haystack.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        match haystack[mid].cmp(&needle) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid,
        }
    }
    None
}

pub fn insertion_sort(v: &mut [i32]) {
    for i in 1..v.len() {
        let key = v[i];
        let mut j = i;
        while j > 0 && v[j - 1] > key {
            v[j] = v[j - 1];
            j -= 1;
        }
        v[j] = key;
    }
}

pub fn is_sorted(v: &[i32]) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
}

pub fn linear_search(v: &[i32], target: i32) -> Option<usize> {
    v.iter().position(|&x| x == target)
}

pub fn count_zeros(v: &[i32]) -> usize {
    v.iter().filter(|&&x| x == 0).count()
}
