// Candidate proof fixture: Option/Result guard before division.

fn ratio_checked(num: u32, den: Option<u32>) -> Result<u32, &'static str> {
    match den {
        Some(value) if value != 0 => Ok(num / value),
        Some(_) => Err("zero denominator"),
        None => Err("missing denominator"),
    }
}

fn main() {
    assert_eq!(ratio_checked(12, Some(3)), Ok(4));
    assert_eq!(ratio_checked(12, Some(0)), Err("zero denominator"));
    assert_eq!(ratio_checked(12, None), Err("missing denominator"));
}
