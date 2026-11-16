pub fn rot(v: &mut Vec<u32>) {
    if !v.is_empty() {
        let f = v.remove(0);
        v.push(f);
    }
}
