//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! One element reached through two slice-pattern spellings is one place: a store
//! through either kills what was known through the other. Each panics on the input
//! named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-29 (an adversarial audit; every one was also
//! proved, and kernel-certified, by the 2026-09-17 pack): a constant pattern index
//! is spelled with the PATTERN's minimum length (`v*[0;min=1]` for `[a, ..]`,
//! `v*[0;min=2]` for `[z, _]`), a subslice rebases it (`v*[1..-0][0;min=1]` is
//! `v*[1;min=2]`), and the place-overlap rule called two distinct literal spellings
//! two places. `slice_pattern_distinct_slots_stay_independent.rs` is the twin.

// v = [0, 0]: `[z, _]` writes element 0, which `[a, ..]` guarded.
pub fn two_minimum_lengths(v: &mut [u8]) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::two_minimum_lengths`
    if let [a, ..] = v {
        if *a < 5 {
            if let [z, _] = v {
                *z = 250;
                if let [b, ..] = v {
                    return *b + 250;
                }
            }
        }
    }
    0
}

// v = [0, 0], buf = [1, 2, 3, 4]: the stale guard bounds an index.
pub fn stale_guard_indexes(v: &mut [u8], buf: &[u8; 4]) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::stale_guard_indexes`
    if let [a, ..] = v {
        if *a < 4 {
            if let [z, _] = v {
                *z = 200;
                if let [b, ..] = v {
                    return buf[*b as usize];
                }
            }
        }
    }
    0
}

// v = [200, 0, 0]: the store's minimum length is 3.
pub fn stale_guard_underflows(v: &mut [u8]) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::stale_guard_underflows`
    if let [a, ..] = v {
        if *a > 100 {
            if let [z, _, _] = v {
                *z = 0;
                if let [b, ..] = v {
                    return *b - 100;
                }
            }
        }
    }
    0
}

// v = [0, 0]: `rest[0]` is `v[1]`.
pub fn through_a_subslice(v: &mut [u8]) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::through_a_subslice`
    if let [_, a, ..] = v {
        if *a < 5 {
            if let [_, rest @ ..] = v {
                if let [r0, ..] = rest {
                    *r0 = 250;
                    if let [_, b, ..] = v {
                        return *b + 250;
                    }
                }
            }
        }
    }
    0
}

pub struct S {
    pub items: [u8; 4],
    pub len: usize,
}

// s.items = [0; 4]: an array field reached through a subslice.
pub fn array_field_subslice(s: &mut S) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::array_field_subslice`
    let [_, a, ..] = s.items;
    if a < 5 {
        let [_, rest @ ..] = &mut s.items;
        let [r0, ..] = rest;
        *r0 = 250;
        let [_, b, ..] = s.items;
        b + 250
    } else {
        0
    }
}

// arr = [0; 4]: the last element, from the end of a subslice.
pub fn from_the_end(arr: &mut [u8; 4]) -> u8 { //~ ERROR failed for `slice_pattern_spellings_alias_refused::from_the_end`
    let [.., a] = *arr;
    if a < 5 {
        let [_, rest @ ..] = arr;
        let [.., z] = rest;
        *z = 250;
        let [.., b] = *arr;
        b + 250
    } else {
        0
    }
}
