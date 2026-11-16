//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `str_char_boundary_test_guards_a_slice.rs`. Each panics on
//! the input named beside it.

// s = "é", n = 1: the slice is on the branch where the test FAILED.
pub fn wrong_branch(s: &str, n: usize) -> &str { //~ ERROR failed for `str_char_boundary_test_guards_a_slice_refused::wrong_branch`
    if !s.is_char_boundary(n) && n <= s.len() { &s[..n] } else { s }
}

// s = "é", t = "ab", n = 1: the test was on another string.
pub fn another_string<'a>(s: &'a str, t: &str, n: usize) -> &'a str { //~ ERROR failed for `str_char_boundary_test_guards_a_slice_refused::another_string`
    if t.is_char_boundary(n) && n <= s.len() { &s[..n] } else { s }
}

// s = "é", n = 0: the slice ends one past the tested index.
pub fn one_past_the_test(s: &str, n: usize) -> &str { //~ ERROR failed for `str_char_boundary_test_guards_a_slice_refused::one_past_the_test`
    if n < s.len() && s.is_char_boundary(n) { &s[..n + 1] } else { s }
}

// s = "ab", a = 2, b = 1: both are boundaries, and `a > b`.
pub fn unordered(s: &str, a: usize, b: usize) -> &str { //~ ERROR failed for `str_char_boundary_test_guards_a_slice_refused::unordered`
    if s.is_char_boundary(a) && s.is_char_boundary(b) { &s[a..b] } else { "" }
}

// s = "é", n = 0: `n` moves after the test.
pub fn moved_after_the_test(s: &str, mut n: usize) -> &str { //~ ERROR failed for `str_char_boundary_test_guards_a_slice_refused::moved_after_the_test`
    if s.is_char_boundary(n) {
        n += 1;
        &s[..n]
    } else {
        s
    }
}
