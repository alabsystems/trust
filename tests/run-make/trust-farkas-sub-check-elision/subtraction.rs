// Trust: the length definition contains Sub, and the final operation needs it.
// The safe guard gives rest.len() >= 4. The twin admits length 5: rest.len() is
// then 3, so the same subtraction really underflows.
#[inline(never)]
pub fn subtract(input: &[u8]) -> Option<usize> {
    #[cfg(not(twin))]
    let minimum = 6;
    #[cfg(twin)]
    let minimum = 5;
    if input.len() < minimum {
        return None;
    }
    let rest = &input[2..];
    Some(rest.len() - 4)
}
