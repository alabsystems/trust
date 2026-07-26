#![crate_type = "lib"]
// Trust: piece #7a — an UNGUARDED const-generic index is OOB-capable; MUST refute.
pub fn cg_unguarded<const N: usize>(a: [u8; N], i: usize) -> u8 { a[i] }
