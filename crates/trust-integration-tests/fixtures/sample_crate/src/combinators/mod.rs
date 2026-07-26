// Functional combinators: higher-order functions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn apply_fn(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

pub fn apply_twice(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    f(f(x))
}

pub fn map_option<T, U>(opt: Option<T>, f: impl FnOnce(T) -> U) -> Option<U> {
    opt.map(f)
}

pub fn flat_map_option<T, U>(opt: Option<T>, f: impl FnOnce(T) -> Option<U>) -> Option<U> {
    opt.and_then(f)
}

pub fn pair_map<T, U>(pair: (T, T), f: impl Fn(T) -> U) -> (U, U) {
    (f(pair.0), f(pair.1))
}
