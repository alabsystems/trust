pub fn div_checked(a: i64, b: i64) -> Option<i64> {
    if b == 0 || (a == i64::MIN && b == -1) { None } else { Some(a / b) }
}
