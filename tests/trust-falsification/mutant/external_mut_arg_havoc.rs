#![crate_type = "lib"]
#![allow(dead_code)]

// SOUNDNESS MUTANT for lever #1 (uninterpreted external calls). An external call
// with a `&mut` argument CAN mutate its referent, so the verifier must NOT model it
// as a no-op fresh-result. Here `std::mem::swap` makes `i` become 99 (out of
// bounds); a buggy "model &mut call as no-op" would leave `i == 0` and FALSELY
// prove `arr[i]` in bounds. The uninterpreted model gates on having NO `&mut`/raw-
// ptr argument, so this call is excluded and keeps failing closed: the obligation
// MUST stay refused (the index is out of bounds, or the function does not lower).
pub fn f(arr: &[u8; 4]) -> u8 {
    let mut i: usize = 0;
    let mut j: usize = 99;
    std::mem::swap(&mut i, &mut j);
    arr[i]
}
