pub fn swap_ends(v: &mut [u32]) {
    let n = v.len();
    if n >= 2 {
        v.swap(0, n - 1);
    }
}
