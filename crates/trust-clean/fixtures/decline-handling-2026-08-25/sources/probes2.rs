#![crate_type = "lib"]
#![feature(register_tool)]
#![register_tool(trust)]
use std::collections::BTreeMap;

// q1: str slice range — char-boundary panic, unmodelled.
pub fn q1_str_range(s: &str, i: usize) -> usize {
    let t = &s[i..];
    t.len()
}

// q2: BTreeMap index — key presence unmodelled.
pub fn q2_btree_index(m: BTreeMap<u32, u32>, k: u32) -> u32 {
    m[&k]
}

// q3: Vec range index with BOTH ends free.
pub fn q3_vec_range2(v: Vec<u8>, a: usize, b: usize) -> usize {
    let s = &v[a..b];
    s.len()
}

// q4: String range index.
pub fn q4_string_range(s: String, end: usize) -> usize {
    let t = &s[..end];
    t.len()
}

// q5: opaque trait-object call feeding a Vec range index.
pub fn q5_dyn_range(v: Vec<u8>, f: &dyn Fn() -> usize) -> usize {
    let s = &v[..f()];
    s.len()
}

// q6: a declined slice row PLUS an ensures — the assumption-authority shape.
#[trust::ensures(result == 3)]
pub fn q6_vec_range_ensures(v: Vec<u8>, end: usize) -> u32 {
    let _s = &v[..end];
    3
}

// q7: VecDeque range index.
pub fn q7_boxslice_range(v: Box<[u8]>, end: usize) -> usize {
    let s = &v[..end];
    s.len()
}
