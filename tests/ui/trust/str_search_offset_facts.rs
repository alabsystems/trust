//@ needs-trust-verify
//@ edition: 2021
//@ revisions: find_prefix find_split find_question find_str_pattern find_multibyte rfind char_local starts_with_len ends_with_len is_empty_len mid_char other_string reseated_root past_match mutated_payload closure_pattern char_local_end affix_false_branch starts_with_short affix_index_o1 affix_reseat_o0 affix_reseat_o1 affix_reseat_o2
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[find_prefix] check-pass
//@[find_split] check-pass
//@[find_question] check-pass
//@[find_str_pattern] check-pass
//@[find_multibyte] check-pass
//@[rfind] check-pass
//@[char_local] check-pass
//@[starts_with_len] check-pass
//@[ends_with_len] check-pass
//@[is_empty_len] check-pass
//@[mid_char] check-fail
//@[other_string] check-fail
//@[reseated_root] check-fail
//@[past_match] check-fail
//@[mutated_payload] check-fail
//@[closure_pattern] check-pass
//@[char_local_end] check-fail
//@[affix_false_branch] check-fail
//@[starts_with_short] check-fail
//@[affix_index_o1] check-pass
//@[affix_index_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[affix_reseat_o0] check-fail
//@[affix_reseat_o0] compile-flags: -Copt-level=0 -Coverflow-checks=on
//@[affix_reseat_o1] check-fail
//@[affix_reseat_o1] compile-flags: -Copt-level=1 -Coverflow-checks=on
//@[affix_reseat_o2] check-fail
//@[affix_reseat_o2] compile-flags: -Copt-level=2 -Coverflow-checks=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (W4 STR-OFFSET, 2026-09-25): the result of an authenticated
//! `str::find`/`rfind` bounds its offset and is a char boundary; a TRUE
//! `str::starts_with`/`ends_with` bounds the length; `str::len`'s call result IS
//! the length. `crates/trust-vcgen/src/generate/str_offset.rs` has the gates;
//! `docs/TCB.md` (`STR_SEARCH_OFFSET`) has the std contract it rests on.
//!
//! The boundary half is STRUCTURAL: a str range endpoint is credited only when it
//! IS the match start `i` or the match END `i + K` with `K` the constant exact
//! match length, over the SAME root string. Every other offset stays under the
//! str char-boundary fail-close.
//!
//! # Before (measured on stage-1 `trustc 0.10.0+gab7e41892`, 2026-09-25)
//!
//! EVERY revision was rc=1. The check-pass ones: `[slice] FAILED` on each str
//! range endpoint (the char-boundary fail-close plus an unbounded offset), plus
//! `[overflow:add] FAILED` on `i + 1` at `i = u64::MAX` where the payload is
//! incremented; `starts_with_len`/`ends_with_len`/`is_empty_len` were
//! `[overflow:sub] FAILED` with `s.len()` a free call result. `find_prefix` is
//! the unaimed `d0/p13`, `find_split` the unaimed `d5/p14`.
//!
//! # The rails, each WITNESSED to panic in a verify-off build
//!
//! * `mid_char` — `&s[i + 1..]` after `find('é')` (a two-byte match): panics
//!   on `"é"` (byte index 1 is not a char boundary).
//! * `other_string` — `t.find(..)`'s offset used on `s`: panics on
//!   `("", "ax")`.
//! * `reseated_root` — the searched root is rebound before the slice: panics on
//!   `("aaax", "b")`.
//! * `past_match` — `i + 2` after a one-byte match: panics on `"x"`.
//! * `mutated_payload` — `i += 10` after the search: panics on `"x"`.
//! * `char_local_end` — `i + 1` after a `char`-LOCAL pattern (width unknown):
//!   panics on `("é", 'é')`.
//! * `affix_false_branch` — `s.len() - 1` on the FALSE branch of
//!   `starts_with`: overflows on `""`.
//! * `starts_with_short` — `s.len() - 3` after `starts_with("ab")`: overflows
//!   on `"ab"`.
//! * `closure_pattern` — a closure pattern was declined (no fact at all); this
//!   one does NOT panic (`&s[..i]` at a char match start is safe) — it was the
//!   disclosed over-refusal, pinned so a widening is a deliberate change. WIDENED
//!   by the merge of 2026-10-14: the soundness line's search-payload credit
//!   (7685c5a2683) holds for every std `Pattern` — a match of a char predicate
//!   starts at a char boundary as a `char` or `&str` match does — so on the merged
//!   stage 1 both rows are proved and kernel-certified; `check-pass` since
//!   2026-10-15. The derived offsets (`past_match`, `mid_char`) stay refused.
//!
//! # The str rails' row since RANGE-DECLINE (re-pinned 2026-10-13)
//!
//! The seven str-range rails above (`mid_char` .. `closure_pattern`) are pinned on
//! the DECLINED row `unsupported MIR `str-range-char-boundary-unmodeled``, an
//! UNKNOWN that strict counts as a build error; they used to pin `[slice] FAILED`.
//! That FAILED was the always-violated `Bool(true)` the str char-boundary
//! fail-close emitted as a refutable `SliceBoundsCheck`: its counterexample was an
//! arbitrary model, not a witness (it FAILED `closure_pattern` too, which does not
//! panic). RANGE-DECLINE (docs/DECISION_QUEUE.md, `c888f21ea31`) made it the
//! `UnsupportedMir` row `str::split_at` already gives; the UI pins were not re-run
//! then (KNOWN_HAZARDS 2026-10-08). Every rail is still `check-fail`, and the pin
//! names the str char-boundary row itself, so a rail that went green, or that was
//! refused on some other row while its str slice proved, fails here. Not restored:
//! a GROUNDED byte-bounds refutation for the rails whose bytes are also out of
//! range (`other_string`, `reseated_root`, `past_match`, `mutated_payload`). The
//! arm emits one row per call, and the declined row stands in for the byte-bounds
//! one (docs/DECISION_QUEUE.md, RANGE-DECLINE-UI-REPIN).
//!
//! # Adversarial round 1 (2026-09-25): the affix fact through the length LICENCE
//!
//! * `affix_reseat_o1` — `let b = s.starts_with("abc"); s = t; if b {
//!   s.as_bytes()[2] }` at `-Copt-level=1`. The MIR is `_3 = starts_with(move _1,
//!   ..); _1 = copy _2; switchInt(_3)`; the `TRUE => len >= 3` fact was stated
//!   through the BARE `_1__slice_len`, which `guards.rs` conjoins after the
//!   version rename, so it bound to `t`'s length: both `SliceBoundsCheck` rows
//!   PROVED, "2 kernel-certified", rc=0 on the w4-alloc-str stage 1
//!   (`0.10.0+gab7e41892` + b06b56569a, probe s91), while `k("abc", "")` panics
//!   "index out of bounds: the len is 0 but the index is 2" (WITNESSED,
//!   verify-off). The fact now goes through `licensed_slice_len_formula`; a
//!   reseated receiver has no licence, so no fact. `affix_reseat_o0` (the
//!   receiver is a reborrow temp) and `affix_reseat_o2` (`starts_with` inlined)
//!   were already refused; they are the twins that keep all three levels pinned.
//! * `affix_index_o1` — the positive twin at `-O1`: the same guard over a
//!   receiver that is never rebound still proves `s.as_bytes()[2]`, so the
//!   licence removed the reseat, not the fact. Its pinned count is 1 obligation
//!   since the rebase onto main 296873da69 (it was 2 at base c2e3daed78): main
//!   no longer emits the second, already-proved `bounds_check:1` row at `-O1`
//!   (main alone: 1 row, `bounds_check:0`, refuted), and the remaining row is
//!   the index this fact proves.

pub enum ParseError {
    MissingAt,
    EmptyLocal,
}

#[cfg(find_prefix)]
pub fn strip_comment(line: &str) -> &str {
    //[find_prefix]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    match line.find('#') {
        Some(i) => &line[..i],
        None => line,
    }
}

#[cfg(find_split)]
pub fn split_at_sign(s: &str) -> Result<(&str, &str), ParseError> {
    //[find_split]~^ NOTE Trust verification: 4 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 5 obligation(s)
    let at = s.find('@').ok_or(ParseError::MissingAt)?;
    let local = &s[..at];
    let domain = &s[at + 1..];
    if local.is_empty() {
        return Err(ParseError::EmptyLocal);
    }
    Ok((local, domain))
}

#[cfg(find_question)]
pub fn after_colon(s: &str) -> Option<&str> {
    //[find_question]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    let i = s.find(':')?;
    Some(&s[i + 1..])
}

#[cfg(find_str_pattern)]
pub fn after_arrow(s: &str) -> &str {
    //[find_str_pattern]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    match s.find("->") {
        Some(i) => &s[i + 2..],
        None => s,
    }
}

#[cfg(find_multibyte)]
pub fn after_e_acute(s: &str) -> &str {
    //[find_multibyte]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    match s.find('é') {
        Some(i) => &s[i + 2..],
        None => s,
    }
}

#[cfg(rfind)]
pub fn basename(path: &str) -> &str {
    //[rfind]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 4 obligation(s)
    match path.rfind('/') {
        Some(i) => &path[i + 1..],
        None => path,
    }
}

#[cfg(char_local)]
pub fn up_to(s: &str, c: char) -> &str {
    //[char_local]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 3 obligation(s)
    match s.find(c) {
        Some(i) => &s[..i],
        None => s,
    }
}

#[cfg(starts_with_len)]
pub fn after_prefix(s: &str) -> usize {
    //[starts_with_len]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if s.starts_with("ab") { s.len() - 2 } else { 0 }
}

#[cfg(ends_with_len)]
pub fn before_suffix(s: &str) -> usize {
    //[ends_with_len]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if s.ends_with('z') { s.len() - 1 } else { 0 }
}

#[cfg(is_empty_len)]
pub fn last_index(s: &str) -> usize {
    //[is_empty_len]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if !s.is_empty() { s.len() - 1 } else { 0 }
}

#[cfg(mid_char)]
pub fn mid_char(s: &str) -> &str {
    //[mid_char]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    match s.find('é') {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

#[cfg(other_string)]
pub fn other_string<'a>(s: &'a str, t: &str) -> &'a str {
    //[other_string]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    match t.find('x') {
        Some(i) => &s[..i],
        None => s,
    }
}

#[cfg(reseated_root)]
pub fn reseated<'a>(a: &'a str, b: &'a str) -> &'a str {
    //[reseated_root]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    let mut s = a;
    if let Some(i) = s.find('x') {
        s = b;
        return &s[..i];
    }
    s
}

#[cfg(past_match)]
pub fn past_match(s: &str) -> &str {
    //[past_match]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    match s.find('x') {
        Some(i) => &s[i + 2..],
        None => s,
    }
}

#[cfg(mutated_payload)]
pub fn mutated(s: &str) -> &str {
    //[mutated_payload]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    if let Some(mut i) = s.find('x') {
        i += 10;
        return &s[..i];
    }
    s
}

#[cfg(closure_pattern)]
pub fn closure_pattern(s: &str) -> &str {
    match s.find(|c: char| c == 'x') {
        Some(i) => &s[..i],
        None => s,
    }
}

#[cfg(char_local_end)]
pub fn after_local(s: &str, c: char) -> &str {
    //[char_local_end]~^ NOTE unsupported MIR `str-range-char-boundary-unmodeled`
    match s.find(c) {
        Some(i) => &s[i + 1..],
        None => s,
    }
}

#[cfg(affix_false_branch)]
pub fn affix_false(s: &str) -> usize {
    //[affix_false_branch]~^ NOTE [overflow:sub] FAILED
    if !s.starts_with('x') { s.len() - 1 } else { 0 }
}

#[cfg(starts_with_short)]
pub fn too_far(s: &str) -> usize {
    //[starts_with_short]~^ NOTE [overflow:sub] FAILED (ay-in-process); counterexample: _3 = 2
    if s.starts_with("ab") { s.len() - 3 } else { 0 }
}

#[cfg(affix_index_o1)]
pub fn third_byte(s: &str) -> u8 {
    //[affix_index_o1]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if s.starts_with("abc") { s.as_bytes()[2] } else { 0 }
}

#[cfg(any(affix_reseat_o0, affix_reseat_o1, affix_reseat_o2))]
pub fn affix_reseat<'a>(mut s: &'a str, t: &'a str) -> u8 {
    //[affix_reseat_o0]~^ NOTE [slice] FAILED (ay-in-process)
    //[affix_reseat_o1]~^^ NOTE [slice] FAILED (ay-in-process)
    //[affix_reseat_o2]~^^^ NOTE [slice] FAILED (ay-in-process)
    let b = s.starts_with("abc");
    s = t;
    if b { s.as_bytes()[2] } else { 0 }
}
