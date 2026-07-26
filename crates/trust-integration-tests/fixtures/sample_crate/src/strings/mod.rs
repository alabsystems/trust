// String and slice operations.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

pub fn is_empty(s: &str) -> bool {
    s.is_empty()
}

pub fn str_len(s: &str) -> usize {
    s.len()
}

pub fn starts_with_hello(s: &str) -> bool {
    s.starts_with("hello")
}

pub fn to_uppercase(s: &str) -> String {
    s.to_uppercase()
}

pub fn trim_whitespace(s: &str) -> &str {
    s.trim()
}

pub fn concat_strs(a: &str, b: &str) -> String {
    format!("{a}{b}")
}

pub fn split_comma(s: &str) -> Vec<&str> {
    s.split(',').collect()
}

pub fn repeat_str(s: &str, n: usize) -> String {
    s.repeat(n)
}
