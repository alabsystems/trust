// slice/str BASELINE family probe — documents the open W20/len gap.
#![allow(dead_code)]

#[inline(never)]
pub fn w_slice_len(v: &[i32]) -> usize {
    v.len()
}

#[inline(never)]
pub fn w_slice_is_empty(v: &[i32]) -> bool {
    v.is_empty()
}

#[inline(never)]
pub fn w_slice_first(v: &[i32]) -> Option<&i32> {
    v.first()
}

#[inline(never)]
pub fn w_slice_last(v: &[i32]) -> Option<&i32> {
    v.last()
}

#[inline(never)]
pub fn w_str_len(s: &str) -> usize {
    s.len()
}

#[inline(never)]
pub fn w_str_is_empty(s: &str) -> bool {
    s.is_empty()
}

#[inline(never)]
pub fn w_array_len(a: &[u8; 16]) -> usize {
    a.len()
}

#[inline(never)]
pub fn w_get_is_some(v: &[i32]) -> bool {
    v.get(0).is_some()
}

#[inline(never)]
pub fn w_len_min_cap(v: &[i32], cap: usize) -> usize {
    v.len().min(cap)
}

fn main() {
    let n = std::env::args().count();
    let data: Vec<i32> = (0..n as i32).collect();
    let v: &[i32] = &data;
    let s: &str = if n > 0 { "hello" } else { "x" };
    let arr = [n as u8; 16];

    let mut acc = 0usize;
    acc += w_slice_len(v);
    acc += w_slice_is_empty(v) as usize;
    acc += w_slice_first(v).map(|x| *x as usize).unwrap_or(0);
    acc += w_slice_last(v).map(|x| *x as usize).unwrap_or(0);
    acc += w_str_len(s);
    acc += w_str_is_empty(s) as usize;
    acc += w_array_len(&arr);
    acc += w_get_is_some(v) as usize;
    acc += w_len_min_cap(v, n);
    println!("{acc}");
}
