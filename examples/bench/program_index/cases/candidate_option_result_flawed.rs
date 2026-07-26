// Candidate proof fixture: flawed Option/Result fallback can divide by zero.

fn ratio_default_zero(num: u32, den: Option<u32>) -> Result<u32, &'static str> {
    Ok(num / den.unwrap_or(0))
}

fn main() {
    assert_eq!(ratio_default_zero(12, Some(3)), Ok(4));
}
