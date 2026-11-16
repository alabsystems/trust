//@ vec-lowering: verifies
//! And building it by `push` verifies too.
fn main() { let mut v: Vec<u32> = Vec::new(); v.push(1); v.push(2); let _ = v.len(); }
