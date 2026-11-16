pub fn join_nums(v: &[u32]) -> String {
    v.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(",")
}
