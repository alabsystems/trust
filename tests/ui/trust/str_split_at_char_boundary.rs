//@ needs-trust-verify
//@ edition: 2021
//@ revisions: len_half len_half_o2 starts_with_mid ends_with_len_minus_1 len_guard starts_with_mut is_empty_guard as_bytes_len_guard find_plus_one starts_with_const ends_with_suffix string_receiver char_indices_for_loop is_char_boundary_guard find_payload find_match_end rfind_match_end zero_and_len split_mut_zero char_indices_yield slice_split char_indices_for_loop_other_root
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[len_half] check-fail
//@[len_half_o2] check-fail
//@[len_half_o2] compile-flags: -Copt-level=2 -Coverflow-checks=on
//@[starts_with_mid] check-fail
//@[ends_with_len_minus_1] check-fail
//@[len_guard] check-fail
//@[starts_with_mut] check-fail
//@[is_empty_guard] check-fail
//@[as_bytes_len_guard] check-fail
//@[find_plus_one] check-fail
//@[starts_with_const] check-fail
//@[ends_with_suffix] check-fail
//@[string_receiver] check-fail
//@[char_indices_for_loop] check-pass
//@[char_indices_for_loop_other_root] check-fail
//@[is_char_boundary_guard] check-fail
//@[find_payload] check-pass
//@[find_match_end] check-pass
//@[rfind_match_end] check-pass
//@[zero_and_len] check-pass
//@[split_mut_zero] check-pass
//@[char_indices_yield] check-pass
//@[slice_split] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (W4 round 3, 2026-09-29): `str::split_at(mid)` / `str::split_at_mut(mid)`
//! panic when `mid > len` OR when `mid` is not a UTF-8 char boundary
//! (`core::str::slice_error_fail`). `str` is extracted as `[u8]`, so only the first
//! half is a formula term, and the call-site `SplitAt` row charged it alone: a
//! proof of `mid <= len` was taken as panic-freedom while the call's
//! `[trust-absent-callee-assumption] core::str::<impl str>::split_at may panic`
//! row was tolerated as runtime-checked. The row now stands only when `mid` is,
//! by structure, a char boundary of the same string (`0`, a `char_indices`
//! offset, a `find`/`rfind` match start or exact match end, or that string's own
//! `len()`); every other `mid` gets the fail-closed
//! `str-split-at-char-boundary-unmodeled` row. See
//! `crates/trust-vcgen/src/generate/panic_calls.rs` (`str_split_at_panic_body`)
//! and `docs/KNOWN_HAZARDS.md`.
//!
//! # The rails, each WITNESSED to panic in a verify-off build
//!
//! Adversarial round 2 (probe dir `w4-salvage/probes/T5-alloc_str-r2`): the
//! driver linked against the VERIFIED rlib panicked (exit 101) with "byte index 1
//! is not a char boundary" on `"é"` (or `"aé"` for `len_half`).
//!
//! * NEW on this branch (rc=0 on the round-2 stage 1 `0.10.0+g7440c3d05`, rc=1 on
//!   main `296873da69`; the branch's `str::len` tie and affix length facts proved
//!   the `mid <= len` half): `len_half` (m40, the everyday
//!   `s.split_at(s.len() / 2)`, and its `-O2` twin), `starts_with_mid` (m10),
//!   `ends_with_len_minus_1` (m13), `len_guard` (m10b), `starts_with_mut` (m41).
//! * PRE-EXISTING on main (rc=0 on `296873da69` too, closed by the same change):
//!   `is_empty_guard` (m42), `as_bytes_len_guard` (m43).
//! * `find_plus_one` (m13b): `split_at(i + 1)` after a two-byte `find('é')` match
//!   — refused before and after (a derived offset is never credited).
//!
//! # Disclosed over-refusals (each a CORRECT program, refused; each rc=1 on main
//! `296873da69` as well)
//!
//! * `starts_with_const` (m33): `split_at(2)` after `starts_with("é")`, and
//!   `ends_with_suffix`: `split_at(s.len() - 2)` after `ends_with("é")`. A
//!   constant (or `len - K`) equal to the affix's byte length is a boundary, but
//!   the credit would have to be path-sensitive to the affix test's true branch;
//!   a constant str range endpoint gets none either. Both were rc=0 on the
//!   round-2 stage 1 (whose numeric-only row accepted them — correctly, by luck
//!   of the constant).
//! * `string_receiver`: `st.find(':')` then `st.split_at(i)` on a `&String` —
//!   each auto-deref is its own `&str` temp, so the search root and the split
//!   root differ. `let s = st.as_str();` first verifies.
//! * `char_indices_for_loop` (CLOSED 2026-10-15, now under Accepted):
//!   `for (i, _) in s.char_indices() { s.split_at(i) }` was refused because the
//!   CharIndices yield lane did not trace the `for` desugaring.
//!
//! # A disclosed over-refusal that main ACCEPTED
//!
//! * `is_char_boundary_guard` (adversarial round 3, q40d): `!s.is_empty() &&
//!   s.is_char_boundary(1)` then `split_at(1)`. Correct, and rc=0 on main
//!   `296873da69` — but only through the numeric-only row that also accepted
//!   the unsound `is_empty_guard` / `as_bytes_len_guard`. A dominating
//!   `is_char_boundary(mid)` test is not credited. The other shapes whose `mid`
//!   main "proved" only numerically (an `is_ascii()` guard, `split_at(1 - 1)`,
//!   `split_at(s.len() - s.len())`) are refused the same way; see the
//!   `str::split_at` entry in `docs/KNOWN_HAZARDS.md`.
//!
//! # Accepted
//!
//! `find_payload` (m45), `find_match_end`, `rfind_match_end`, `zero_and_len`
//! (m44), `split_mut_zero` and `char_indices_yield`: each `mid` is a boundary by
//! `core::str`'s own contract, credited structurally over the SAME root string.
//! `char_indices_for_loop` joins them on the merged tree (2026-10-15): the
//! soundness line's `for`-loop CharIndices yield (7685c5a2683, "a for-loop yield is
//! a str slice endpoint") traces the desugaring that main's lane did not, so the
//! split row is proved (the loop's `next` keeps its own `runtime_checked` row, a
//! default-policy warning). Its NEGATIVES stay refused, measured on that stage 1
//! (`char_indices_for_loop_other_root`): the offsets of ANOTHER string, the offset
//! plus one, and a root rebound inside the loop each keep the
//! `str-split-at-char-boundary-unmodeled` Unknown.
//! `slice_split` is the `[u8]` control: a byte slice has no char boundaries, so
//! its row is the numeric `mid > len` alone (the ordinary sweep's `t32`).

#[cfg(any(len_half, len_half_o2))]
pub fn halves(s: &str) -> (&str, &str) {
    //[len_half]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::halves`
    //[len_half]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    //[len_half_o2]~^^^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::halves`
    //[len_half_o2]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    s.split_at(s.len() / 2)
}

#[cfg(starts_with_mid)]
pub fn after_first_byte(s: &str) -> (&str, &str) {
    //[starts_with_mid]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::after_first_byte`
    //[starts_with_mid]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.starts_with("é") { s.split_at(1) } else { ("", "") }
}

#[cfg(ends_with_len_minus_1)]
pub fn before_last_byte(s: &str) -> (&str, &str) {
    //[ends_with_len_minus_1]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::before_last_byte`
    //[ends_with_len_minus_1]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.ends_with("é") { s.split_at(s.len() - 1) } else { ("", "") }
}

#[cfg(len_guard)]
pub fn len_guarded(s: &str) -> (&str, &str) {
    //[len_guard]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::len_guarded`
    //[len_guard]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.len() >= 2 { s.split_at(1) } else { ("", "") }
}

#[cfg(starts_with_mut)]
pub fn first_half_mut(s: &mut str) -> usize {
    //[starts_with_mut]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::first_half_mut`
    //[starts_with_mut]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.starts_with("é") {
        let (a, _b) = s.split_at_mut(1);
        a.len()
    } else {
        0
    }
}

#[cfg(is_empty_guard)]
pub fn non_empty(s: &str) -> (&str, &str) {
    //[is_empty_guard]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::non_empty`
    //[is_empty_guard]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if !s.is_empty() { s.split_at(1) } else { ("", "") }
}

#[cfg(as_bytes_len_guard)]
pub fn byte_len_guarded(s: &str) -> (&str, &str) {
    //[as_bytes_len_guard]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::byte_len_guarded`
    //[as_bytes_len_guard]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let b = s.as_bytes();
    if b.len() >= 2 { s.split_at(1) } else { ("", "") }
}

#[cfg(find_plus_one)]
pub fn past_accent(s: &str) -> Option<(&str, &str)> {
    //[find_plus_one]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::past_accent`
    //[find_plus_one]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let i = s.find('é')?;
    Some(s.split_at(i + 1))
}

#[cfg(starts_with_const)]
pub fn after_prefix(s: &str) -> (&str, &str) {
    //[starts_with_const]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::after_prefix`
    //[starts_with_const]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.starts_with("é") { s.split_at(2) } else { ("", "") }
}

#[cfg(ends_with_suffix)]
pub fn before_suffix(s: &str) -> (&str, &str) {
    //[ends_with_suffix]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::before_suffix`
    //[ends_with_suffix]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if s.ends_with("é") { s.split_at(s.len() - 2) } else { (s, "") }
}

#[cfg(string_receiver)]
pub fn string_split(st: &String) -> Option<(&str, &str)> {
    //[string_receiver]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::string_split`
    //[string_receiver]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let i = st.find(':')?;
    Some(st.split_at(i))
}

#[cfg(char_indices_for_loop)]
pub fn has_empty_prefix(s: &str) -> bool {
    let mut seen = false;
    for (i, _) in s.char_indices() {
        let (a, _) = s.split_at(i);
        if a.is_empty() {
            seen = true;
        }
    }
    seen
}

/// The offsets of ANOTHER string are not boundaries of `s`.
#[cfg(char_indices_for_loop_other_root)]
pub fn other_root(s: &str, t: &str) -> bool {
    //[char_indices_for_loop_other_root]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::other_root`
    //[char_indices_for_loop_other_root]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let mut seen = false;
    for (i, _) in t.char_indices() {
        let (a, _) = s.split_at(i);
        if a.is_empty() {
            seen = true;
        }
    }
    seen
}

/// A boundary plus one byte is not a boundary.
#[cfg(char_indices_for_loop_other_root)]
pub fn plus_one(s: &str) -> bool {
    //[char_indices_for_loop_other_root]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::plus_one`
    //[char_indices_for_loop_other_root]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let mut seen = false;
    for (i, _) in s.char_indices() {
        let (a, _) = s.split_at(i + 1);
        if a.is_empty() {
            seen = true;
        }
    }
    seen
}

/// The split root is rebound inside the loop to another string.
#[cfg(char_indices_for_loop_other_root)]
pub fn shadowed_root(s: &str, t: &str) -> bool {
    //[char_indices_for_loop_other_root]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::shadowed_root`
    //[char_indices_for_loop_other_root]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    let mut seen = false;
    let mut u = s;
    for (i, _) in s.char_indices() {
        u = t;
        let (a, _) = u.split_at(i);
        if a.is_empty() {
            seen = true;
        }
    }
    let _ = u;
    seen
}

#[cfg(is_char_boundary_guard)]
pub fn checked_boundary(s: &str) -> (&str, &str) {
    //[is_char_boundary_guard]~^ ERROR Trust Level 0 safety verification incomplete for `str_split_at_char_boundary::checked_boundary`
    //[is_char_boundary_guard]~| NOTE unsupported MIR `str-split-at-char-boundary-unmodeled`
    if !s.is_empty() && s.is_char_boundary(1) { s.split_at(1) } else { (s, "") }
}

#[cfg(find_payload)]
pub fn split_colon(s: &str) -> Option<(&str, &str)> {
    //[find_payload]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    let i = s.find(':')?;
    Some(s.split_at(i))
}

#[cfg(find_match_end)]
pub fn after_arrow(s: &str) -> Option<&str> {
    //[find_match_end]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    let i = s.find("->")?;
    Some(s.split_at(i + 2).1)
}

#[cfg(rfind_match_end)]
pub fn after_last_slash(s: &str) -> Option<(&str, &str)> {
    //[rfind_match_end]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    let i = s.rfind('/')?;
    Some(s.split_at(i + 1))
}

#[cfg(zero_and_len)]
pub fn ends(s: &str) -> ((&str, &str), (&str, &str)) {
    //[zero_and_len]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    (s.split_at(s.len()), s.split_at(0))
}

#[cfg(split_mut_zero)]
pub fn empty_head_mut(s: &mut str) -> usize {
    //[split_mut_zero]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    let (a, _) = s.split_at_mut(0);
    a.len()
}

#[cfg(char_indices_yield)]
pub fn after_first_char(s: &str) -> &str {
    //[char_indices_yield]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    let mut chars = s.char_indices();
    chars.next();
    if let Some((i, _)) = chars.next() { s.split_at(i).1 } else { "" }
}

#[cfg(slice_split)]
pub fn bytes_split(v: &[u8], i: usize) -> (&[u8], &[u8]) {
    //[slice_split]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)
    v.split_at(i.min(v.len()))
}
