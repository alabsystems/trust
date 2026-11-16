//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The `Some` index of `str::find` / `str::rfind` is a match start: a char boundary
//! of the searched string and at most its length (below it for a `char` pattern),
//! whatever the pattern. So is an index `for (i, c) in s.char_indices()` yields.
//!
//! MEASURED OVER-REFUSAL, 2026-09-29, on the ordinary-Rust sweep (p08, p28, p37):
//! `&s[..i]` after `find` failed closed on the char-boundary check (a str slice
//! endpoint had to be a `char_indices` yield taken with `next`, or 0), `i + 1` after
//! `rfind` was refuted with `i = usize::MAX`, and a `for` loop over `char_indices`
//! did not count as the `next` the credit looked for. The refusing twins are in
//! `str_find_payload_is_a_char_boundary_refused.rs`. The slice rows prove; a
//! `find`/`rfind` call's own panic-freedom keeps its runtime check on the default lane.

pub fn key_of(s: &str) -> &str {
    match s.find('=') {
        Some(i) => &s[..i],
        None => s,
    }
}

pub fn value_from(s: &str) -> &str {
    match s.find("=>") {
        Some(i) => &s[i..],
        None => "",
    }
}

// REFUSED since the merge of 2026-10-14, by main's fail-closed rule for a std routine
// handed a closure, not by this file's subject: the `&s[..i]` row is proved, but the
// closure's bundled `char::is_whitespace` keeps a `runtime_checked` member row, so the
// `find` call over it is an unproved generic absent callee and keeps the function
// fail-closed (measured on the merged stage 1, 2026-10-15). `key_of`, `value_from` and
// `ext` (`char` and `&str` patterns) still build. The char-boundary credit itself holds
// for a closure pattern (`str_search_offset_facts.rs#closure_pattern`, check-pass).
pub fn head_by_closure(s: &str) -> &str {
    //~^ ERROR Trust strict verification failed for `str_find_payload_is_a_char_boundary::head_by_closure`
    match s.find(|c: char| c.is_whitespace()) {
        Some(i) => &s[..i],
        None => s,
    }
}

pub fn ext(s: &str) -> Option<&str> {
    let i = s.rfind('.')?;
    s.get(i + 1..)
}

pub fn byte_at_match(s: &str) -> u8 {
    match s.find('x') {
        Some(i) => s.as_bytes()[i],
        None => 0,
    }
}

pub fn rest_after_space(s: &str) -> &str {
    for (i, c) in s.char_indices() {
        if c == ' ' {
            return &s[i..];
        }
    }
    ""
}
