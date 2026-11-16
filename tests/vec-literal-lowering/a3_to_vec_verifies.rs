//@ vec-lowering: verifies
//! A WORKING EQUIVALENT of a1, byte-for-byte the same value.
fn main() { let v: Vec<u32> = [1u32, 2, 3].to_vec(); let _ = v.len(); }
