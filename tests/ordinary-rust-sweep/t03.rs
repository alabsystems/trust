pub fn lookup<T: Copy>(v: &[T], i: usize) -> Option<T> {
    if i < v.len() { Some(v[i]) } else { None }
}
