pub fn mid(v: &[u32]) -> Option<u32> {
    if v.is_empty() { None } else { Some(v[v.len() / 2]) }
}
