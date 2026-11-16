pub fn min_max(v: &[i32]) -> Option<(i32, i32)> {
    let mn = v.iter().copied().min()?;
    let mx = v.iter().copied().max()?;
    Some((mn, mx))
}
