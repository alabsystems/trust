// Source of `tests/fixtures/slice_tuple_*_mir.json` (see
// `tests/slice_tuple_pattern_len_realmir.rs`). Line numbers are load-bearing.

pub fn pair_of_slices(idx: &[u32], ops: &[u64]) -> u64 {
    match (idx, ops) {
        ([w], [e]) => (*w as u64) ^ *e,
        _ => 0,
    }
}

pub fn tuple_of_slices(name: &str, idx: &[u32], ops: &[u64]) -> u64 {
    match (name, idx, ops) {
        ("a", [w], []) => *w as u64,
        ("b", [w], [e]) => (*w as u64) ^ *e,
        (_, [h, l], [e]) => (*h as u64) ^ (*l as u64) ^ *e,
        _ => 0,
    }
}

// COUNTER: the arm checks the FIRST slice's length only; `b[0]` indexes the
// second, unchecked one and panics for `b = &[]`.
pub fn other_field_unchecked(a: &[u8], b: &[u8]) -> u8 {
    match (a, b) {
        ([x], _) => *x ^ b[0],
        _ => 0,
    }
}

// COUNTER: the tuple's field is reseated after the arm matched it; the index on
// the NEW slice is unchecked and panics for `c = &[]`.
pub fn reseated_field(a: &[u8], b: &[u8], c: &[u8]) -> u8 {
    let mut t = (a, b);
    match t {
        ([_], _) => {
            t.0 = c;
            t.0[0]
        }
        _ => 0,
    }
}

// The shape trust-mc-trust-vc-ingest's `lower_indexed_app` had before
// trust-mc ae2157707 rewrote it: a `&str`, a slice of enum values matched by
// variant, and a `Vec::as_slice()` result, one arm behind a match guard.
pub enum Index {
    Numeral(String),
    Symbol(String),
}

pub fn indexed_app(name: &str, indices: &[Index], lowered: Vec<u64>) -> Result<u64, ()> {
    match (name, indices, lowered.as_slice()) {
        (literal, [Index::Numeral(width)], [])
            if literal.strip_prefix("bv").is_some_and(|v| !v.is_empty()) =>
        {
            Ok(width.len() as u64)
        }
        ("int2bv", [Index::Numeral(width)], [expr]) => Ok(width.len() as u64 ^ *expr),
        ("zero_extend", [Index::Numeral(extra)], [expr]) => Ok(extra.len() as u64 ^ *expr),
        ("extract", [Index::Numeral(high), Index::Numeral(low)], [expr]) => {
            Ok((high.len() ^ low.len()) as u64 ^ *expr)
        }
        _ => Err(()),
    }
}
