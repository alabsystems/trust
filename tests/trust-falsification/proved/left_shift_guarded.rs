#![crate_type = "lib"]
// A left shift whose amount is provably < 64. The shift-amount obligation
// `Or([k < 0, k >= 64])` is UNSAT under the `k < 64` guard, so the native CHC
// lane PROVES it. rustc can only insert a runtime panic for a variable shift;
// -full certifies it statically. Pairs with mutant/left_shift_guarded.rs.
pub fn left_shift_guarded(k: u32) -> Option<u64> {
    if k < 64 { Some(1u64 << k) } else { None }
}
