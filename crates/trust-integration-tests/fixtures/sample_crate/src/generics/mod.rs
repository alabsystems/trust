// Generic functions with trait bounds.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn identity<T>(x: T) -> T {
    x
}

pub fn first<T>(a: T, _b: T) -> T {
    a
}

pub fn max_generic<T: PartialOrd>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

pub fn min_generic<T: PartialOrd>(a: T, b: T) -> T {
    if a < b { a } else { b }
}

pub fn swap<T>(pair: (T, T)) -> (T, T) {
    (pair.1, pair.0)
}

pub fn unwrap_or_default<T: Default>(val: Option<T>) -> T {
    val.unwrap_or_default()
}

pub fn contains<T: PartialEq>(slice: &[T], item: &T) -> bool {
    slice.iter().any(|x| x == item)
}

pub fn all_match<T: PartialEq>(slice: &[T], val: &T) -> bool {
    slice.iter().all(|x| x == val)
}
