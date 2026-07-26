#![crate_type = "lib"]
// Trust: piece #7b — an unguarded index into an internally-built [x;N]. MUST refute.
pub fn repeat_unguarded<const N: usize>(i: usize) -> u8 {
    let a = [0u8; N];
    a[i]
}
