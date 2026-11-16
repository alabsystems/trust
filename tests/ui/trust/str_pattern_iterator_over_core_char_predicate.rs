//@ needs-trust-verify
//@ edition: 2021
//@ revisions: rsplit_whitespace split_whitespace user_fn_pattern
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[rsplit_whitespace] check-fail
//@[split_whitespace] check-fail
//@[user_fn_pattern] check-fail
//! **A `str` pattern iterator over a core char predicate is total (Trust, 2026-09-28).**
//!
//! `s.rsplit(char::is_whitespace).next()` (the ordinary sweep's s08) was refused under
//! `certify` for three reasons:
//! * the compiler bundled `RSplit::next`, because `total_std_iterator_ty` admitted no
//!   pattern-carrying `str` iterator. It now admits the `Split` family when the pattern
//!   type is one of core's own `Pattern` impls, checked on the real type
//!   (`str_pattern_ty_is_core`);
//! * the bridge's receiver gates rejected the stored predicate as a fn item. A core
//!   char-classification predicate is now trusted (`fn_def_is_core_char_predicate`);
//! * `callee_is_trait_method_in` cannot parse a callee with a `->` in its `Self`
//!   (`docs/KNOWN_HAZARDS.md`), so the method is recognized by its exact tail
//!   (`str_iter_fn_item_pattern_method`).
//!
//! * `rsplit_whitespace`, `split_whitespace`: POSITIVE.
//! * `user_fn_pattern`: the NEGATIVE. A user fn item runs user code, which here can
//!   panic, so `f` stays refused. The annotation on `f` discriminates. `sep` fails on its
//!   own as well, so unannotated errors are allowed.

#[cfg(rsplit_whitespace)]
pub fn f(s: &str) -> &str {
    //[rsplit_whitespace]~^ ERROR Trust strict verification failed for `str_pattern_iterator_over_core_char_predicate::f`
    // CAPABILITY LOSS (certify), re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // main's SYS-CALLABLE-1 refuses, under `certify`, a std function handed to generic code
    // as a value unless its own MIR is shown unable to panic; `char::is_whitespace` is not (its
    // Unicode table lookup), and this line's by-name trust of core char predicates
    // (`fn_def_is_core_char_predicate`) does not override that conjunct. The default policy
    // still builds it. Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    s.rsplit(char::is_whitespace).next().unwrap_or("")
}

#[cfg(split_whitespace)]
pub fn f(s: &str) -> Option<&str> {
    //[split_whitespace]~^ ERROR Trust strict verification failed for `str_pattern_iterator_over_core_char_predicate::f`
    // See `rsplit_whitespace` (CAPABILITY LOSS (certify), re-pinned 2026-10-15).
    s.split(char::is_whitespace).next()
}

#[cfg(user_fn_pattern)]
fn sep(c: char) -> bool {
    assert!(c != 'x');
    c == ','
}

#[cfg(user_fn_pattern)]
pub fn f(s: &str) -> &str {
    //[user_fn_pattern]~^ ERROR Trust Level 0 safety verification incomplete for `str_pattern_iterator_over_core_char_predicate::f`
    s.rsplit(sep).next().unwrap_or("")
}
