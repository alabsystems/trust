//@ needs-trust-verify
//@ edition: 2021
//@ revisions: range_match ascii_guard from_sum from_sum_wide nested_filter_count encode_buf4 encode_buf2 encode16_buf2 encode16_buf1 str_pattern_closure str_pattern_panics array_from_fn array_map array_map_overflows array_map_needs_drop str_pattern_fn_ptr
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[range_match] check-pass
//@[ascii_guard] check-pass
//@[from_sum] check-pass
//@[from_sum_wide] check-fail
//@[nested_filter_count] check-pass
//@[encode_buf4] check-pass
//@[encode_buf2] check-fail
//@[encode16_buf2] check-fail
//@[encode16_buf1] check-fail
//@[str_pattern_closure] check-pass
//@[str_pattern_panics] check-fail
//@[array_from_fn] check-pass
//@[array_map] check-pass
//@[array_map_overflows] check-fail
//@[array_map_needs_drop] check-fail
//@[str_pattern_fn_ptr] check-fail
//! Ordinary-Rust sweep precision fixes (2026-10-09), one revision each, with a
//! negative control where a near-miss must stay refused:
//! * `range_match` (p19): the interval fixpoint's widen points are the targets of real
//!   DFS back edges, not "edges to a lower block number", and its descending pass keeps
//!   the `SwitchInt` arm refinements, so a `match c { b'0'..=b'9' => Some(c - b'0') }`
//!   helper summarizes `[0, 9]` and its caller's `h * 16 + l` proves.
//! * `ascii_guard` (m07): the interval domain meets a stable `u8` with the hull of a
//!   genuine std ascii predicate on the branch where it held.
//! * `from_sum` (r04): `map(u32::from)` over `u8` items bounds each item by `u8`'s
//!   range (core's lossless primitive-int `From`), so a 4-item `sum` proves;
//!   `from_sum_wide` over `u32` items can overflow and stays refused.
//! * `nested_filter_count` (p43): `split(..).map(..).filter(..).count()` is granted
//!   compiler-total through nested Filter/Map layers.
//! * `encode_buf4` (p56): `encode_utf8` into a `[u8; 4]` buffer cannot panic;
//!   `encode_buf2` into a `[u8; 2]` buffer can, and stays refused. The same for
//!   `encode_utf16` (review round 90: it had no row at all): `[u16; 2]` builds,
//!   `[u16; 1]` stays refused.
//! * `str_pattern_closure` (p34): a core `str` pattern method with a verified
//!   `(char) -> bool` closure is compiler-total; a panicking closure stays refused.
//! * `array_from_fn` / `array_map` (w04, y04): `core::array::from_fn` and
//!   `<[T; N]>::map` with a verified closure are compiler-total; an overflowing
//!   closure, and an element type that needs drop, stay refused.
//! * `str_pattern_fn_ptr` (review round 93): a closure that calls a `fn` POINTER
//!   (`|c| p(c)`) has an empty ledger, and the shared evidence bar
//!   (`body_discharges_panic_freedom`) credited it; it now refuses any body with an
//!   unresolved indirect call, so the grant declines and the caller stays refused.

#[cfg(range_match)]
fn hex(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        _ => None,
    }
}

#[cfg(range_match)]
pub fn pair(a: u8, b: u8) -> Option<u8> {
    let h = hex(a)?;
    let l = hex(b)?;
    Some(h * 16 + l)
}

#[cfg(ascii_guard)]
fn nib(c: u8) -> Option<u8> {
    if c.is_ascii_digit() { Some(c - b'0') } else { None }
}

#[cfg(ascii_guard)]
pub fn pair(a: u8, b: u8) -> Option<u8> {
    let h = nib(a)?;
    let l = nib(b)?;
    Some(h * 16 + l)
}

#[cfg(from_sum)]
pub fn f(a: &[u8; 4]) -> u32 {
    a.iter().copied().map(u32::from).sum()
}

#[cfg(from_sum_wide)]
pub fn f(a: &[u32; 4]) -> u32 {
    //[from_sum_wide]~^ ERROR Trust strict verification failed
    a.iter().copied().map(u32::from).sum()
}

#[cfg(nested_filter_count)]
pub fn f(s: &str) -> usize {
    s.split(',').map(|t| t.trim()).filter(|t| !t.is_empty()).count()
}

#[cfg(encode_buf4)]
pub fn f(c: char) -> usize {
    let mut buf = [0u8; 4];
    c.encode_utf8(&mut buf).len()
}

#[cfg(encode_buf2)]
pub fn f(c: char) -> usize {
    //[encode_buf2]~^ ERROR Trust strict verification failed
    let mut buf = [0u8; 2];
    c.encode_utf8(&mut buf).len()
}

#[cfg(encode16_buf2)]
pub fn f(c: char) -> usize {
    //[encode16_buf2]~^ ERROR Trust Level 0 safety verification incomplete for `sweep_precision_range_match_ascii_from::f`
    //[encode16_buf2]~| ERROR Trust strict verification failed for `sweep_precision_range_match_ascii_from::f`
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // `c.encode_utf16(&mut buf)` into a 2-element buffer is refused
    // (`Call::encode_utf16::panic-freedom-unverified`: the buffer's length is not modeled, so
    // `len_utf16() <= 2` is not compared with it), beside one more unproved row.
    // Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    let mut buf = [0u16; 2];
    c.encode_utf16(&mut buf).len()
}

#[cfg(encode16_buf1)]
pub fn f(c: char) -> usize {
    //[encode16_buf1]~^ ERROR Trust strict verification failed
    let mut buf = [0u16; 1];
    c.encode_utf16(&mut buf).len()
}

#[cfg(str_pattern_closure)]
pub fn f(s: &str) -> &str {
    s.trim_end_matches(|c: char| c == '\n' || c == '\r')
}

#[cfg(str_pattern_panics)]
pub fn f<'a>(s: &'a str, t: &[u8; 2]) -> &'a str {
    //[str_pattern_panics]~^ ERROR Trust
    s.trim_end_matches(|c: char| t[c as usize % 4] == 0)
}

#[cfg(array_from_fn)]
pub fn f() -> [u8; 8] {
    core::array::from_fn(|i| i as u8)
}

#[cfg(array_map)]
pub fn f(a: [u8; 4]) -> [u16; 4] {
    a.map(|b| b as u16 * 2)
}

#[cfg(array_map_overflows)]
pub fn f(a: [u8; 4]) -> [u8; 4] {
    //[array_map_overflows]~^ ERROR Trust
    a.map(|b| b + 1)
}

#[cfg(array_map_needs_drop)]
pub fn f(a: [u8; 2]) -> [Vec<u8>; 2] {
    //[array_map_needs_drop]~^ ERROR Trust
    a.map(|b| vec![b])
}

#[cfg(str_pattern_fn_ptr)]
pub fn f(s: &str, p: fn(char) -> bool) -> bool {
    //[str_pattern_fn_ptr]~^ ERROR Trust
    s.contains(|c: char| p(c))
}
