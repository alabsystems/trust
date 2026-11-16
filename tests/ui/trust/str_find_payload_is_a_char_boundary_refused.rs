//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twins of `str_find_payload_is_a_char_boundary.rs`. Each panics on
//! the input named beside it.

// "é": the match is two bytes long, so one past its start is inside it.
pub fn past_the_match_start(s: &str) -> &str { //~ ERROR failed for `str_find_payload_is_a_char_boundary_refused::past_the_match_start`
    match s.find('é') {
        Some(i) => &s[..i + 1],
        None => s,
    }
}

// s = "a=", t = "é": an index into `s` is not a boundary of `t`.
pub fn another_string<'a>(s: &str, t: &'a str) -> &'a str { //~ ERROR failed for `str_find_payload_is_a_char_boundary_refused::another_string`
    match s.find('=') {
        Some(i) => &t[..i],
        None => t,
    }
}

// Any s: the empty pattern's last match starts at the end, one past the last byte.
pub fn byte_at_empty_match(s: &str) -> u8 { //~ ERROR failed for `str_find_payload_is_a_char_boundary_refused::byte_at_empty_match`
    match s.rfind("") {
        Some(i) => s.as_bytes()[i],
        None => 0,
    }
}

// "é": one past a yielded index is inside a two-byte char.
pub fn one_past_the_char(s: &str) -> &str { //~ ERROR failed for `str_find_payload_is_a_char_boundary_refused::one_past_the_char`
    for (i, c) in s.char_indices() {
        if c == 'é' {
            return &s[i + 1..];
        }
    }
    ""
}
