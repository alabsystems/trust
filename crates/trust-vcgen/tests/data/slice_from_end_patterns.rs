// Source of `tests/fixtures/slice_from_end_*_mir.json` (see
// `tests/slice_from_end_pattern_realmir.rs`). Line numbers are load-bearing.

pub fn last_of(a: &[u8]) -> u8 {
    match a {
        [.., x] => *x,
        _ => 0,
    }
}

pub fn second_last(a: &[u8]) -> u8 {
    match a {
        [.., x, _] => *x,
        _ => 0,
    }
}

pub fn last_of_array(a: [u8; 1]) -> u8 {
    let [.., x] = a;
    x
}

pub fn ends_of_pair(a: &[u8], b: &[u8]) -> u8 {
    match (a, b) {
        ([.., x], [y, _, ..]) => *x ^ *y,
        _ => 0,
    }
}

// A `Subslice` beside a tuple field: `rest` is `a[1..]` (from-end `[1:0]`).
// The pattern guarantees `rest.len() >= 1`, not `>= 2`, so `rest[1]` panics for
// `a.len() == 2` and its bounds assert must refute; the subslice itself is in
// range.
pub fn subslice_rest(a: &[u8], b: &[u8]) -> u8 {
    match (a, b) {
        ([_, rest @ ..], [y]) => rest[1] ^ *y,
        _ => 0,
    }
}
