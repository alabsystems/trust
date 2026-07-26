#![crate_type = "lib"]
// Trust: piece #7a — an inclusive bound `i <= N` admits `i == N` (OOB); MUST refute.
pub fn cg_off_by_one<const N: usize>(a: [u8; N], i: usize) -> u8 {
    if i <= N { a[i] } else { 0 }
}
