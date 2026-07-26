#![crate_type = "lib"]
// A GUARDED owned-Vec scalar WRITE: `if i < v.len() { v[i] = x }`. The
// `IndexMut::index_mut` receiver reborrows `&mut (*v)` — length-BENIGN (Vec's
// IndexMut never resizes), so the length-stability gate keeps the abstract
// length AND the `_len == coll_len(v)` guard tie; the `i >= len` obligation is
// discharged by the dominating guard. Write-path twin of the #7c read idiom.
pub fn set_at(v: &mut Vec<i32>, i: usize, x: i32) {
    if i < v.len() {
        v[i] = x;
    }
}
