pub fn any_upper(v: &[&str]) -> bool {
    v.iter().any(|s| s.chars().any(|c| c.is_uppercase()))
}
