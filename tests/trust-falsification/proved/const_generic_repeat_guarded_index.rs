#![crate_type = "lib"]
// Trust: piece #7b — an INTERNALLY-BUILT `[x; N]` (Rvalue::Repeat, N a const
// param) carries the same symbolic length, so a guarded index PROVES.
pub fn repeat_guarded<const N: usize>(i: usize) -> u8 {
    let a = [0u8; N];
    if i < N { a[i] } else { 0 }
}
