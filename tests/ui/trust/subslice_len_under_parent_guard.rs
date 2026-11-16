//@ needs-trust-verify
//@ edition: 2021
//@ revisions: from range range_sym to nested split_at sym_start array inplace
//@ revisions: from_offby1 from_noguard from_wrong_offset range_wrong to_wrong split_at_wrong
//@ revisions: nested_wrong other_parent sym_start_offby1 array_wrong
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[from] check-pass
//@[range] check-pass
//@[range_sym] check-pass
//@[to] check-pass
//@[nested] check-pass
//@[split_at] check-pass
//@[sym_start] check-pass
//@[array] check-pass
//@[inplace] check-pass
//@[from_offby1] check-fail
//@[from_noguard] check-fail
//@[from_wrong_offset] check-fail
//@[range_wrong] check-fail
//@[to_wrong] check-fail
//@[split_at_wrong] check-fail
//@[nested_wrong] check-fail
//@[other_parent] check-fail
//@[sym_start_offby1] check-fail
//@[array_wrong] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//! Trust (2026-10-15, TRUST-KI-1015-1, RANGE-INDEX-RESULT-LEN): a sub-slice's length is
//! its range's (`generate::range_index_len`).
//!
//! # Before (measured on the channel seal `b58a105dde`, raw `trustc`, 2026-10-15)
//!
//! Every `check-pass` revision was refuted: `rest.len() - k` read `[overflow:sub] FAILED`
//! (in-process `ay`) on a model with the sub-slice's length 0 beside a parent that the
//! guard makes long enough, because the length of `&s[a..]` / `&s[a..b]` / `&s[..b]` /
//! `s.split_at(mid)` was a free name.
//!
//! # The refused rails, each a program whose subtraction really underflows
//!
//! * `from_offby1` — guard `len >= 5` for `&s[2..]` and `- 4` (`len == 5`);
//! * `from_noguard` — no guard (the index alone gives `len >= 2`);
//! * `from_wrong_offset` — `&s[3..]` under the guard written for `&s[2..]`;
//! * `range_wrong`, `to_wrong`, `split_at_wrong`, `array_wrong` — the subtraction one wider
//!   than the range's length;
//! * `nested_wrong` — a sub-slice of a sub-slice cut one too deep;
//! * `other_parent` — the guard is on another slice;
//! * `sym_start_offby1` — a symbolic start whose guard is one short.
//!
//! Each refused revision names the row that must fail, a `~^ NOTE [overflow:sub] FAILED` annotation
//! scoped to that revision under its `fn` line: the compiler attaches each unproved row's verdict
//! to the function's verification report as a note with no span of its own, so compiletest reads it
//! at the `fn` line, and each of these functions has exactly one subtraction. A revision refused
//! for another row while its subtraction is proved no longer passes. The function-level errors stay
//! unannotated (`dont-require-annotations: ERROR`): their text counts every unproved row, and
//! `from_noguard`'s unguarded `&input[2..]` (`[slice] FAILED`) is one more.

#[cfg(from)]
pub fn from(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    Some(rest.len() - 4)
}

#[cfg(range)]
pub fn range(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..5];
    Some(rest.len() - 3)
}

#[cfg(range_sym)]
pub fn range_sym(input: &[u8]) -> Option<usize> {
    if input.len() < 7 {
        return None;
    }
    let rest = &input[2..input.len() - 1];
    Some(rest.len() - 4)
}

#[cfg(to)]
pub fn to(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[..5];
    Some(rest.len() - 5)
}

#[cfg(nested)]
pub fn nested(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    let rest2 = &rest[1..];
    Some(rest2.len() - 3)
}

#[cfg(split_at)]
pub fn split_at(input: &[u8]) -> Option<usize> {
    if input.len() < 6 {
        return None;
    }
    let (_head, tail) = input.split_at(2);
    Some(tail.len() - 4)
}

#[cfg(sym_start)]
pub fn sym_start(input: &[u8], k: usize) -> Option<usize> {
    if k > 100 || input.len() < k + 4 {
        return None;
    }
    let rest = &input[k..];
    Some(rest.len() - 4)
}

#[cfg(array)]
pub fn array(arr: &[u8; 8]) -> usize {
    let rest = &arr[2..];
    rest.len() - 6
}

#[cfg(inplace)]
pub fn inplace(input: &[u8]) -> Option<usize> {
    let mut s = input;
    if s.len() < 6 {
        return None;
    }
    s = &s[2..];
    Some(s.len() - 4)
}

#[cfg(from_offby1)]
pub fn from_offby1(input: &[u8]) -> Option<usize> {
    //[from_offby1]~^ NOTE [overflow:sub] FAILED
    if input.len() < 5 {
        return None;
    }
    let rest = &input[2..];
    Some(rest.len() - 4)
}

#[cfg(from_noguard)]
pub fn from_noguard(input: &[u8]) -> usize {
    //[from_noguard]~^ NOTE [overflow:sub] FAILED
    let rest = &input[2..];
    rest.len() - 4
}

#[cfg(from_wrong_offset)]
pub fn from_wrong_offset(input: &[u8]) -> Option<usize> {
    //[from_wrong_offset]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 {
        return None;
    }
    let rest = &input[3..];
    Some(rest.len() - 4)
}

#[cfg(range_wrong)]
pub fn range_wrong(input: &[u8]) -> Option<usize> {
    //[range_wrong]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..5];
    Some(rest.len() - 4)
}

#[cfg(to_wrong)]
pub fn to_wrong(input: &[u8]) -> Option<usize> {
    //[to_wrong]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 {
        return None;
    }
    let rest = &input[..5];
    Some(rest.len() - 6)
}

#[cfg(split_at_wrong)]
pub fn split_at_wrong(input: &[u8]) -> Option<usize> {
    //[split_at_wrong]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 {
        return None;
    }
    let (_head, tail) = input.split_at(2);
    Some(tail.len() - 5)
}

#[cfg(nested_wrong)]
pub fn nested_wrong(input: &[u8]) -> Option<usize> {
    //[nested_wrong]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 {
        return None;
    }
    let rest = &input[2..];
    let rest2 = &rest[3..];
    Some(rest2.len() - 2)
}

#[cfg(other_parent)]
pub fn other_parent(input: &[u8], other: &[u8]) -> Option<usize> {
    //[other_parent]~^ NOTE [overflow:sub] FAILED
    if input.len() < 6 || other.len() < 2 {
        return None;
    }
    let rest = &other[2..];
    Some(rest.len() - 4)
}

#[cfg(sym_start_offby1)]
pub fn sym_start_offby1(input: &[u8], k: usize) -> Option<usize> {
    //[sym_start_offby1]~^ NOTE [overflow:sub] FAILED
    if k > 100 || input.len() < k + 3 {
        return None;
    }
    let rest = &input[k..];
    Some(rest.len() - 4)
}

#[cfg(array_wrong)]
pub fn array_wrong(arr: &[u8; 8]) -> usize {
    //[array_wrong]~^ NOTE [overflow:sub] FAILED
    let rest = &arr[2..];
    rest.len() - 7
}
